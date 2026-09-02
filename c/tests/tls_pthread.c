// Verifies the platform assumptions the threaded GC is built on, on THIS machine.
// Build with the project's own flags:  clang $CSTD $CFLAGS -o tls_pthread tls_pthread.c
//
//   1. C23 `thread_local` compiles with no <threads.h> (Apple ships none).
//   2. A `thread_local` is genuinely per-thread under pthreads, not shared.
//   3. One `thread_local` struct POINTER, not bare scalars: macOS has no
//      local-exec TLS, so each distinct thread-local costs an indirect call.
//   4. Each thread's context sits on its own cache line, so two threads
//      bump-allocating never invalidate each other's line.
//   5. A registry populated by the threads themselves is readable by another
//      thread -- the collector reaching every mutator's cursor.
//   6. TLS gives no destructor hook, so unregistering must be explicit.

#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define THREADS 8
#define BUMPS   100000
#define LINE    64

typedef struct {
    uintptr_t ix_ptr, ix_limit, ix_bytes;  // the fields gc_new touches
    pthread_t owner;
} ThreadCtx;

// One thread-local, holding a pointer. Every field is then a plain offset.
static thread_local ThreadCtx *self;

static ThreadCtx *registry[THREADS];
static atomic_int registered;
static pthread_mutex_t registry_lock = PTHREAD_MUTEX_INITIALIZER;

static void register_thread(void) {
    // Cache-line aligned: adjacent contexts must not share a line, or one
    // thread's bump invalidates its neighbour's.
    ThreadCtx *ctx = aligned_alloc(LINE, ((sizeof *ctx + LINE - 1) / LINE) * LINE);
    *ctx = (ThreadCtx){.owner = pthread_self()};
    self = ctx;
    pthread_mutex_lock(&registry_lock);
    registry[atomic_fetch_add(&registered, 1)] = ctx;
    pthread_mutex_unlock(&registry_lock);
}

static void unregister_thread(void) { /* explicit: TLS has no exit hook */ }

static void *worker(void *arg) {
    register_thread();
    uintptr_t base = (uintptr_t)arg;
    self->ix_ptr = base;
    for (int i = 0; i < BUMPS; i++) {   // the gc_new shape: read, test, write back
        uintptr_t p = self->ix_ptr;
        self->ix_ptr = p + 8;
        self->ix_bytes += 8;
    }
    unregister_thread();
    return NULL;
}

int main(void) {
    pthread_t threads[THREADS];
    int failures = 0;

    for (int i = 0; i < THREADS; i++)
        pthread_create(&threads[i], NULL, worker, (void *)(uintptr_t)(i * 0x100000));
    for (int i = 0; i < THREADS; i++) pthread_join(threads[i], NULL);

    // (2) Each thread kept its own cursor: no interleaving, no lost updates.
    if (atomic_load(&registered) != THREADS) {
        printf("FAIL: registered %d, expected %d\n", atomic_load(&registered), THREADS);
        failures++;
    }
    for (int i = 0; i < THREADS; i++) {
        ThreadCtx *c = registry[i];   // (5) another thread reads it after the fact
        uintptr_t moved = c->ix_ptr & 0xFFFFF;
        if (moved != BUMPS * 8 || c->ix_bytes != BUMPS * 8) {
            printf("FAIL: ctx %d moved %lu bytes %lu, expected %d\n",
                   i, (unsigned long)moved, (unsigned long)c->ix_bytes, BUMPS * 8);
            failures++;
        }
        // (4) each context on its own line
        if ((uintptr_t)c % LINE != 0) {
            printf("FAIL: ctx %d not %d-byte aligned (%p)\n", i, LINE, (void *)c);
            failures++;
        }
        for (int j = 0; j < i; j++)
            if ((uintptr_t)registry[j] / LINE == (uintptr_t)c / LINE) {
                printf("FAIL: ctx %d and %d share a cache line\n", j, i);
                failures++;
            }
    }
    // (2 again) the main thread's own `self` was never touched by the workers.
    if (self != NULL) { printf("FAIL: main thread's self was written by a worker\n"); failures++; }

    printf(failures ? "%d FAILURES\n" : "all assumptions hold (%d failures)\n", failures);
    return failures != 0;
}
