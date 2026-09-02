// M3: the collector under real threads, with no Marmelade surface yet.
//
// Each case is one the design says must work, and each fails in a way that is
// otherwise invisible -- a lost root frees a live object and crashes somewhere
// unrelated an hour later, and a missed poll simply hangs.
//
//   1. N threads allocating hard, forcing collections against each other.
//   2. N threads reading one published immutable graph while collections run.
//   3. A thread in a NON-ALLOCATING loop -- it reaches no allocator poll, so
//      without the back-edge poll the collector waits for it forever.
//   4. A thread blocked in read() -- it cannot poll at all, so without the
//      blocking bracket the collector waits for it forever.
//
// Build: clang $CSTD $CFLAGS -I c -pthread -o threads_stress \
//              c/tests/threads_stress.c c/gc.c c/runtime.c
// A hang is a failure: run it under a timeout.

#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "gc.h"
#include "runtime.h"

#define THREADS 8
#ifndef ALLOCS
#define ALLOCS  20000   // -DALLOCS=200 for MARM_GC_STRESS, which is ~1000x slower
#endif

static atomic_int failures;
static Value shared_graph;          // published once, read by everyone
static atomic_bool stop_spinning;

// A generated program supplies this table of its globals; here it is the one
// shared graph, so the collector treats it as a precise root just as it would a
// top-level binding.
Value *const gc_user_roots[] = {&shared_graph};
const size_t gc_user_roots_count = 1;

static void fail(const char *what) {
    fprintf(stderr, "FAIL: %s\n", what);
    atomic_fetch_add(&failures, 1);
}

// ---- 1. everyone allocates, so everyone triggers collections ---------------
static void *allocator(void *arg) {
    gc_register_thread(&arg);
    for (int i = 0; i < ALLOCS; i++) {
        // A LARGE object every so often: past IX_MAX_ALLOC these skip the bump path
        // entirely for malloc plus the shared large_set/gc_large, which is a
        // different route under a different lock. billions hits it on every chunk
        // (a 47521-bucket table) and the original driver never did.
        if ((i & 0x3F) == 0) {
            Value big = mk_tuple_uninit(200);
            for (size_t k = 0; k < 200; k++) as_tuple(big)->elems[k] = VInt((int64_t)k);
            if (as_int(proj(big, 199)) != 199) fail("large object readback");
        }
        // A small tree, immediately garbage: maximum pressure, no survivors.
        Value a = mk_data1(0, VInt(i));
        Value b = mk_data2(1, a, VInt(i * 2));
        Value c = mk_tuple3(a, b, VInt(i));
        if (as_int(data_field(b, 1)) != i * 2) fail("field readback after alloc");
        if (as_int(proj(c, 2)) != i) fail("tuple readback after alloc");
    }
    gc_unregister_thread();
    return NULL;
}

// ---- 2. everyone reads one shared immutable graph ---------------------------
static void *reader(void *arg) {
    gc_register_thread(&arg);
    for (int i = 0; i < ALLOCS; i++) {
        // Walk the published graph. If a collection freed it -- a lost root, a
        // missed stack -- this reads garbage or segfaults.
        Value head = shared_graph;
        for (int depth = 0; depth < 8; depth++) {
            if (as_int(data_field(head, 1)) != depth) fail("shared graph corrupted");
            head = data_field(head, 0);
        }
        (void)mk_data1(0, VInt(i)); // allocate too, so collections keep firing
    }
    gc_unregister_thread();
    return NULL;
}

// ---- 3. a loop that allocates nothing --------------------------------------
// The optimiser's intended output, not an edge case. Without a back-edge poll
// this thread never checks in and every collection waits for it forever.
static void *spinner(void *arg) {
    gc_register_thread(&arg);
    volatile unsigned long n = 0;
    while (!atomic_load_explicit(&stop_spinning, memory_order_relaxed)) {
        n++;
        gc_poll();   // what codegen emits at a loopified back edge
    }
    gc_unregister_thread();
    return NULL;
}

// ---- 4. a thread blocked in the kernel -------------------------------------
// It cannot poll: it is asleep in read(). The bracket publishes its roots and
// lets the collector count it as parked.
static void *blocker(void *arg) {
    int *fds = arg;
    gc_register_thread(&arg);
    char byte;
    enter_blocking_call();
    ssize_t got = read(fds[0], &byte, 1);   // blocks until main writes
    leave_blocking_call();
    if (got != 1) fail("blocking read returned nothing");
    (void)mk_data1(0, VInt(1));             // allocate again after returning
    gc_unregister_thread();
    return NULL;
}

int main(void) {
    Value anchor = VInt(0);
    gc_init(&anchor);

    // A small immutable chain, rooted in a global so it survives everything.
    shared_graph = mk_data2(1, VInt(-1), VInt(7));
    for (int depth = 7; depth >= 0; depth--)
        shared_graph = mk_data2(1, shared_graph, VInt(depth));

    int fds[2];
    if (pipe(fds) != 0) { perror("pipe"); return 1; }

    pthread_t allocators[THREADS], readers[THREADS], spin, block;
    pthread_create(&spin, NULL, spinner, NULL);
    pthread_create(&block, NULL, blocker, fds);
    for (int i = 0; i < THREADS; i++) pthread_create(&allocators[i], NULL, allocator, NULL);
    for (int i = 0; i < THREADS; i++) pthread_create(&readers[i], NULL, reader, NULL);

    // Joining BLOCKS, and this thread is registered with the collector, so it must
    // hand over its roots first -- otherwise every collection waits for a thread
    // that is asleep in pthread_join and can never poll. (This is why the real
    // `Thread.join` has to bracket its wait too.)
    enter_blocking_call();
    for (int i = 0; i < THREADS; i++) pthread_join(allocators[i], NULL);
    for (int i = 0; i < THREADS; i++) pthread_join(readers[i], NULL);
    leave_blocking_call();

    // Release the two stragglers only after every collection has happened, so
    // they really were parked/foreign across them.
    atomic_store(&stop_spinning, true);
    if (write(fds[1], "x", 1) != 1) fail("pipe write");
    enter_blocking_call();
    pthread_join(spin, NULL);
    pthread_join(block, NULL);
    leave_blocking_call();

    // The shared graph must have survived every collection intact.
    Value head = shared_graph;
    for (int depth = 0; depth < 8; depth++) {
        if (as_int(data_field(head, 1)) != depth) fail("shared graph lost after joins");
        head = data_field(head, 0);
    }

    int n = atomic_load(&failures);
    printf(n ? "%d FAILURES\n" : "all threaded GC cases pass (%d failures)\n", n);
    return n != 0;
}
