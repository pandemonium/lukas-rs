# The native compiler flags every Marmelade program is built with. Sourced by
# both compile-lady.sh and c/run.sh so the test panel cannot drift away from the
# way programs are actually compiled -- it did once, and the panel spent that
# time exercising unoptimised binaries nobody runs.
#
# `-flto` earns its place beyond speed: it turns latent "raw word sitting in a
# Value slot" bugs into loud failures instead of letting them ride on whether the
# word happens to be odd.
#
# Override by exporting CFLAGS before invoking either script.
: "${CFLAGS:=-O2 -flto}"
