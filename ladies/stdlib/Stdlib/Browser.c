#include "gc.h"
#include <stdlib.h>

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#include <string.h>

typedef struct {
    Value model;
} BrowserState;

static Value browser_dispatch;
static bool browser_dispatch_pinned;

/* Pointer, key and frame events carry records or numbers, not text, so each kind
   has its own Lady callback, registered once by `raw_set_dispatchers`. */
static Value browser_pointer_dispatch;
static Value browser_key_dispatch;
static Value browser_frame_dispatch;
static bool browser_dispatchers_pinned;

typedef struct Pending {
    int id;
    Value callback;
    struct Pending *next;
} Pending;

static Pending *pending_requests;
static int next_request_id = 1;

static Pending *pending_new(Value callback)
{
    Pending *request = malloc(sizeof *request);
    if (!request) abort();
    request->id = next_request_id++;
    request->callback = callback;
    request->next = pending_requests;
    pending_requests = request;
    gc_pin(&request->callback);
    return request;
}

static Pending *pending_take(int id)
{
    Pending **link = &pending_requests;
    while (*link && (*link)->id != id) link = &(*link)->next;
    if (!*link) return NULL;
    Pending *request = *link;
    *link = request->next;
    return request;
}

static void pending_finish(Pending *request, Value result)
{
    if (!request) return;
    (void)apply(request->callback, result);
    gc_unpin(&request->callback);
    free(request);
}

static const uint8_t *text_bytes(Value text) { return slice_ptr(text); }
static int text_length(Value text) { return (int)slice_len(text); }

extern void browser_dom_begin(const uint8_t *root, int root_len);

extern void browser_dom_open(int space, int keyed, const uint8_t *name, int name_len);

extern void browser_dom_close(void);

extern void browser_dom_text(const uint8_t *body, int body_len);

extern void browser_dom_key(const uint8_t *key, int key_len);

extern void browser_dom_attribute(const uint8_t *name, int name_len, const uint8_t *value, int value_len);

extern void browser_dom_event(const uint8_t *name, int name_len, int index);

// The subtree just drawn is the last child of the open element; file it.
extern void browser_dom_lazy_store(int id);

// Insert a subtree filed by an earlier render. It is the very same object, which is
// what lets the reconciler skip it.
extern void browser_dom_lazy_reuse(int id);

extern void browser_dom_lazy_keep(int id);

extern void browser_dom_finish(void);

// Switch the document-level listeners to match the program's subscriptions. The
// listeners are installed once and consult the flags; the frame loop runs only
// while a frame subscription exists.
extern void browser_subscribe(int frame, int key_down, int key_up);

extern double browser_time_now(void);

extern char * browser_local_storage_get(const uint8_t *key, int key_len);

extern void browser_local_storage_set(const uint8_t *key, int key_len, const uint8_t *value, int value_len);

extern void browser_local_storage_remove(const uint8_t *key, int key_len);

extern void browser_local_storage_clear(void);

extern void browser_yield(int request);

extern void browser_fetch_get(const uint8_t *url, int url_len, int request);

extern void browser_web_socket_connect(const uint8_t *url, int url_len, int request);

extern int browser_web_socket_send(int handle, const uint8_t *body, int body_len);

extern void browser_web_socket_receive(int handle, int request);

extern void browser_web_socket_close(int handle);

EMSCRIPTEN_KEEPALIVE
void marmelade_browser_dispatch(int index, const char *payload)
{
    if (!browser_dispatch_pinned) return;
    Value callback = browser_dispatch;
    Value with_index = apply(callback, VInt(index));
    (void)apply(with_index, mk_text(payload));
}

EMSCRIPTEN_KEEPALIVE
void marmelade_browser_dispatch_pointer(int index, int x, int y, int button, int shift)
{
    if (!browser_dispatchers_pinned) return;
    /* Records use the compiler's canonical label order: Button, Shift, X, Y. */
    Value pointer = mk_tuple4(VInt(button), VBool(shift != 0), VInt(x), VInt(y));
    (void)apply(apply(browser_pointer_dispatch, VInt(index)), pointer);
}

EMSCRIPTEN_KEEPALIVE
void marmelade_browser_dispatch_key(int kind, const char *code, const char *key, int flags)
{
    if (!browser_dispatchers_pinned) return;
    Value code_text = mk_text(code);
    Value key_text = mk_text(key);
    /* Canonical label order: Code, Ctrl, Key, Repeat, Shift. */
    Value record = mk_tuple(5, code_text, VBool((flags & 4) != 0), key_text,
                            VBool((flags & 1) != 0), VBool((flags & 2) != 0));
    (void)apply(apply(browser_key_dispatch, VInt(kind)), record);
}

EMSCRIPTEN_KEEPALIVE
void marmelade_browser_dispatch_frame(int time)
{
    if (!browser_dispatchers_pinned) return;
    (void)apply(browser_frame_dispatch, VInt(time));
}

EMSCRIPTEN_KEEPALIVE
void marmelade_fetch_complete(int request_id, int status,
                               const char *body, int body_length)
{
    Pending *request = pending_take(request_id);
    /* Records use the compiler's canonical label order: Body, then Status. */
    Value response = mk_tuple2(mk_textn(body, (size_t)body_length), VInt(status));
    pending_finish(request, response);
}

EMSCRIPTEN_KEEPALIVE
void marmelade_browser_yielded(int request_id)
{
    pending_finish(pending_take(request_id), VUnit());
}

EMSCRIPTEN_KEEPALIVE
void marmelade_web_socket_connected(int request_id, int handle)
{
    pending_finish(pending_take(request_id), VInt(handle));
}

EMSCRIPTEN_KEEPALIVE
void marmelade_web_socket_received(int request_id, int succeeded,
                                    const char *body, int body_length)
{
    Value result = succeeded
        ? perhaps_this(mk_textn(body, (size_t)body_length))
        : perhaps_nope();
    pending_finish(pending_take(request_id), result);
}

FOREIGN_DECL(int64_t, Root_Stdlib_Browser_raw_state_new, Value, model, {
    BrowserState *state = malloc(sizeof *state);
    if (!state) abort();
    state->model = model;
    gc_pin(&state->model);
    return (int64_t)(uintptr_t)state;
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_state_get, int64_t, raw, {
    return ((BrowserState *)(uintptr_t)raw)->model;
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_state_set, int64_t, raw, Value, model, {
    ((BrowserState *)(uintptr_t)raw)->model = model;
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_begin, Value, root, {
    browser_dom_begin(text_bytes(root), text_length(root));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_open,
             int64_t, space, Bool, keyed, Value, name, {
    browser_dom_open((int)space, keyed ? 1 : 0, text_bytes(name), text_length(name));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_key, Value, key, {
    browser_dom_key(text_bytes(key), text_length(key));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_store, int64_t, id, {
    browser_dom_lazy_store((int)id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_reuse, int64_t, id, {
    browser_dom_lazy_reuse((int)id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_keep, int64_t, id, {
    browser_dom_lazy_keep((int)id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_close, Value, unit, {
    (void)unit;
    browser_dom_close();
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_text, Value, body, {
    browser_dom_text(text_bytes(body), text_length(body));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_attribute,
             Value, name, Value, value, {
    browser_dom_attribute(text_bytes(name), text_length(name),
                          text_bytes(value), text_length(value));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_event,
             Value, name, int64_t, index, {
    browser_dom_event(text_bytes(name), text_length(name), (int)index);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_finish, Value, callback, {
    if (!browser_dispatch_pinned) {
        browser_dispatch = callback;
        gc_pin(&browser_dispatch);
        browser_dispatch_pinned = true;
    }
    browser_dom_finish();
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_set_dispatchers,
             Value, pointer, Value, key, Value, frame, {
    browser_pointer_dispatch = pointer;
    browser_key_dispatch = key;
    browser_frame_dispatch = frame;
    if (!browser_dispatchers_pinned) {
        gc_pin(&browser_pointer_dispatch);
        gc_pin(&browser_key_dispatch);
        gc_pin(&browser_frame_dispatch);
        browser_dispatchers_pinned = true;
    }
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_subscribe,
             Bool, frame, Bool, key_down, Bool, key_up, {
    browser_subscribe(frame ? 1 : 0, key_down ? 1 : 0, key_up ? 1 : 0);
    return VUnit();
})

FOREIGN_DECL(int64_t, Root_Stdlib_Browser_raw_time_now, Value, unit, {
    (void)unit;
    return (int64_t)browser_time_now();
})

/* Identity for `Lazy`: the value itself, compared by its word. The collector is
   non-moving, so a word names one object for that object's whole life. */
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_erase, Value, value, {
    return value;
})

FOREIGN_DECL(Bool, Root_Stdlib_Browser_raw_same, Value, left, Value, right, {
    return left.w == right.w;
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_yield, Value, callback, {
    Pending *request = pending_new(callback);
    browser_yield(request->id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_get, Value, key, {
    char *value = browser_local_storage_get(text_bytes(key), text_length(key));
    if (!value) return perhaps_nope();
    Value result = perhaps_this(mk_text(value));
    free(value);
    return result;
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_set,
             Value, key, Value, value, {
    browser_local_storage_set(text_bytes(key), text_length(key),
                              text_bytes(value), text_length(value));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_remove, Value, key, {
    browser_local_storage_remove(text_bytes(key), text_length(key));
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_clear, Value, unit, {
    (void)unit;
    browser_local_storage_clear();
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_fetch_get,
             Value, url, Value, callback, {
    Pending *request = pending_new(callback);
    browser_fetch_get(text_bytes(url), text_length(url), request->id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_connect,
             Value, url, Value, callback, {
    Pending *request = pending_new(callback);
    browser_web_socket_connect(text_bytes(url), text_length(url), request->id);
    return VUnit();
})

FOREIGN_DECL(Bool, Root_Stdlib_Browser_raw_web_socket_send,
             int64_t, handle, Value, body, {
    return browser_web_socket_send((int)handle, text_bytes(body), text_length(body));
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_receive,
             int64_t, handle, Value, callback, {
    Pending *request = pending_new(callback);
    browser_web_socket_receive((int)handle, request->id);
    return VUnit();
})

FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_close, int64_t, handle, {
    browser_web_socket_close((int)handle);
    return VUnit();
})

#else

/* Stdlib's parent module currently imports every declared child eagerly, so a
   native program that never references Browser still emits foreign closure
   initialisers for this file.  Capability resolution rejects every reachable
   Browser operation before C emission; these bodies only satisfy those inert
   closure definitions until module loading becomes demand-driven. */
static void browser_unavailable(void) { abort(); }

FOREIGN_DECL(int64_t, Root_Stdlib_Browser_raw_state_new, Value, model, {
    (void)model; browser_unavailable(); return 0;
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_state_get, int64_t, state, {
    (void)state; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_state_set,
             int64_t, state, Value, model, {
    (void)state; (void)model; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_begin, Value, value, {
    (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_open,
             int64_t, space, Bool, keyed, Value, name, {
    (void)space; (void)keyed; (void)name; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_key, Value, key, {
    (void)key; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_store, int64_t, id, {
    (void)id; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_reuse, int64_t, id, {
    (void)id; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_lazy_keep, int64_t, id, {
    (void)id; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_set_dispatchers,
             Value, pointer, Value, key, Value, frame, {
    (void)pointer; (void)key; (void)frame; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_subscribe,
             Bool, frame, Bool, key_down, Bool, key_up, {
    (void)frame; (void)key_down; (void)key_up; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(int64_t, Root_Stdlib_Browser_raw_time_now, Value, unit, {
    (void)unit; browser_unavailable(); return 0;
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_erase, Value, value, {
    (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Bool, Root_Stdlib_Browser_raw_same, Value, left, Value, right, {
    (void)left; (void)right; browser_unavailable(); return false;
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_close, Value, value, {
    (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_text, Value, value, {
    (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_attribute,
             Value, name, Value, value, {
    (void)name; (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_event,
             Value, name, int64_t, index, {
    (void)name; (void)index; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_dom_finish, Value, callback, {
    (void)callback; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_yield, Value, callback, {
    (void)callback; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_get, Value, key, {
    (void)key; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_set,
             Value, key, Value, value, {
    (void)key; (void)value; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_remove, Value, key, {
    (void)key; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_local_storage_clear, Value, unit, {
    (void)unit; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_fetch_get,
             Value, url, Value, callback, {
    (void)url; (void)callback; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_connect,
             Value, url, Value, callback, {
    (void)url; (void)callback; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Bool, Root_Stdlib_Browser_raw_web_socket_send,
             int64_t, handle, Value, body, {
    (void)handle; (void)body; browser_unavailable(); return false;
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_receive,
             int64_t, handle, Value, callback, {
    (void)handle; (void)callback; browser_unavailable(); return VUnit();
})
FOREIGN_DECL(Value, Root_Stdlib_Browser_raw_web_socket_close,
             int64_t, handle, {
    (void)handle; browser_unavailable(); return VUnit();
})

#endif
