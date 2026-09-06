// Runtime half of compiler-side partial escape analysis for immutable slices.
// Build with:
//   clang -std=c23 -O2 -flto -pthread -I c -o borrowed_slices \
//     c/tests/borrowed_slices.c c/gc.c c/runtime.c

#include <assert.h>
#include <string.h>

#include "gc.h"
#include "runtime.h"

Value *const gc_user_roots[] = {NULL};
const size_t gc_user_roots_count = 0;

static Value captured(Value self, Value ignored) {
    (void)ignored;
    return env_get(self, 0);
}

int main(void) {
    int stack_bottom;
    gc_init(&stack_bottom);
    runtime_init();

    Value owner = mk_text("abcdef");
    Slice slot;
    Value borrowed = slice_sub_borrowed(owner, 1, 3, &slot);
    assert(is_borrowed(borrowed));
    assert(slice_len(borrowed) == 3);
    assert(memcmp(slice_ptr(borrowed), "bcd", 3) == 0);

    Value ordinary = slice_sub(owner, 1, 3);
    assert(val_eq(borrowed, ordinary));
    assert(as_bool(prim_text_eq(borrowed, ordinary)));

    Value tuple = mk_tuple1(borrowed);
    Value tuple_child = proj(tuple, 0);
    assert(!is_borrowed(tuple_child));
    assert(as_bool(prim_text_eq(tuple_child, ordinary)));

    Value data = mk_data1(0, borrowed);
    Value data_child = data_field(data, 0);
    assert(!is_borrowed(data_child));
    assert(as_bool(prim_text_eq(data_child, ordinary)));

    static const ClosureDesc descriptor = {captured, NULL, 1};
    Value closure = mk_closure_d1(&descriptor, borrowed);
    Value capture = apply(closure, VUnit());
    assert(!is_borrowed(capture));
    assert(as_bool(prim_text_eq(capture, ordinary)));

    Value elements[] = {borrowed};
    Value array = mk_flat_array_from(1, elements);
    Value array_child = flat_array_get_word(array, 0, 0);
    assert(!is_borrowed(array_child));
    assert(as_bool(prim_text_eq(array_child, ordinary)));

    Value pinned = borrowed;
    gc_pin(&pinned);
    assert(!is_borrowed(pinned));
    gc_unpin(&pinned);

    // The backing object is reachable only through the stack descriptor when
    // the escape barrier triggers its stress collection.
    Slice temporary_slot;
    Value temporary = slice_sub_borrowed(mk_text("xyz"), 1, 2, &temporary_slot);
    Value escaped = mk_tuple1(temporary);
    assert(memcmp(slice_ptr(proj(escaped, 0)), "yz", 2) == 0);

    return 0;
}
