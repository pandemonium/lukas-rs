# The native compiler flags every Marmelade program is built with. Sourced by
# both compile-lady.sh and c/run.sh so the test panel cannot drift away from the
# way programs are actually compiled -- it did once, and the panel spent that
# time exercising unoptimised binaries nobody runs.
#
# `-flto` earns its place beyond speed: it turns latent "raw word sitting in a
# Value slot" bugs into loud failures instead of letting them ride on whether the
# word happens to be odd.
#
# CSTD is separate from CFLAGS so an override of one does not silently drop the
# other. C23 for `thread_local`: Apple ships no <threads.h>, so under C11 the only
# spelling is `_Thread_local`, which C23 deprecates.
#
# Override by exporting CSTD or CFLAGS before invoking either script.
: "${CSTD:=-std=c23}"
: "${CFLAGS:=-O2 -flto -pthread}"
