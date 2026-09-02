// Companion implementation of Stdlib.Threading's `foreign` primitives.
//
// The whole interface to the collector is `gc_register_thread` / `gc_unregister_thread`:
// a thread reports ITSELF, so nothing here knows about `ix_ptr` and nothing in the
// collector knows about `Thread.spawn` (notes/threading.md).
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>

#include "gc.h"

// `IO α = Suspend (Unit -> α)`, so the action handed to `spawn` is already a heap
// closure: the child just applies it. Both `action` and `result` are pinned --
// `action` because between `spawn` returning and the child starting, this struct is
// its only reference; `result` because it outlives the thread that produced it and
// the joiner does not hold it yet. Neither window is covered by any stack scan.
typedef struct {
    pthread_t tid;
    Value action;
    Value result;
} MarmThread;

static void *marm_thread_entry(void *arg) {
    MarmThread *t = arg;
    // `&arg` is this frame: the highest address the thread will use, so everything
    // it allocates lives below and the conservative scan covers it.
    gc_register_thread(&arg);
    t->result = apply(t->action, VUnit());
    gc_unregister_thread();
    return NULL;
}

// raw_spawn : (Unit -> α) -> Int   (the handle, as an integer; see Threading.lady)
FOREIGN_DECL(int64_t, Root_Stdlib_Threading_Thread_raw_spawn, Value, action, {
    MarmThread *t = calloc(1, sizeof *t);
    t->action = action;
    t->result = VUnit();
    gc_pin(&t->action);
    gc_pin(&t->result);
    // No error channel on `spawn` yet, and there is no sound value to return: the
    // result type is `∀α`, so handing back a Unit would fabricate a value of
    // whatever type the caller expected. Fail loudly rather than quietly wrong --
    // if spawn ever needs to be recoverable, it must return a `Result` and this
    // becomes a fault instead.
    if (pthread_create(&t->tid, NULL, marm_thread_entry, t) != 0) {
        fprintf(stderr, "marmelade: Thread.spawn could not create a thread\n");
        abort();
    }
    return (int64_t)(intptr_t)t;
})

// raw_join : Int -> α
FOREIGN_DECL(Value, Root_Stdlib_Threading_Thread_raw_join, int64_t, handle, {
    MarmThread *t = (MarmThread *)(intptr_t)handle;
    // `spawn` aborts rather than returning a null handle, and `Thread` is opaque,
    // so a caller cannot fabricate one.
    assert(t != NULL);
    // Joining BLOCKS, and this thread is registered with the collector. Without the
    // bracket it sleeps in `pthread_join` where it can never poll, and every
    // collection waits for it forever -- a hang, reproduced in c/tests/threads_stress.c.
    enter_blocking_call();
    pthread_join(t->tid, NULL);
    leave_blocking_call();

    Value result = t->result;
    gc_unpin(&t->action);
    gc_unpin(&t->result);
    free(t);
    return result;
})


// ---------------------------------------------------------------- work queue
// A shared cursor over `count` units of work, handed out one at a time. This is
// what makes a fixed pool of workers self-balancing: a worker that finishes early
// simply takes the next index, so a slow one (an efficiency core, a chunk with more
// distinct keys) delays only itself. The spawn-per-item shape cannot do that -- with
// one thread per item, a straggler is a whole core's worth of work stuck behind it.
//
// A single relaxed fetch-add. There is nothing to order here: each index is claimed
// by exactly one worker, and the memory the worker then touches is reachable from
// its own arguments. Contention is one atomic per CHUNK (hundreds), not per row.
typedef struct {
    _Atomic long long next;
    long long count;
} WorkQueue;

// raw_queue_new : Int -> Int   (unit count -> handle)
FOREIGN_DECL(int64_t, Root_Stdlib_Threading_Work_Queue_raw_new, int64_t, count, {
    WorkQueue *q = malloc(sizeof *q);
    atomic_init(&q->next, 0);
    q->count = count;
    return (int64_t)(intptr_t)q;
})

// raw_queue_next : Int -> Int   (handle -> next index, or -1 when drained)
FOREIGN_DECL(int64_t, Root_Stdlib_Threading_Work_Queue_raw_next, int64_t, handle, {
    WorkQueue *q = (WorkQueue *)(intptr_t)handle;
    long long i = atomic_fetch_add_explicit(&q->next, 1, memory_order_relaxed);
    return i < q->count ? (int64_t)i : (int64_t)-1;
})

// raw_queue_free : Int -> Unit
FOREIGN_DECL(Value, Root_Stdlib_Threading_Work_Queue_raw_free, int64_t, handle, {
    free((void *)(intptr_t)handle);
    return VUnit();
})
