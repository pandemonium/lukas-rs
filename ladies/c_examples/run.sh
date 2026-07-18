#!/usr/bin/env sh
# The foreign-function gallery, run and output-checked through the C backend (mc
# → C → clang → run). These programs declare `foreign` functions with no
# interpreter body, so the C backend + each module's companion `<dir>/*.c` is the
# only way to run them. See ladies/c_panel.sh for the pipeline and status tokens.
exec sh "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)/c_panel.sh" c_examples
