#!/usr/bin/env sh
# The example gallery, run and output-checked through the C backend (mc → C →
# clang → run). See ladies/c_panel.sh for the pipeline and status tokens.
exec sh "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)/c_panel.sh" examples
