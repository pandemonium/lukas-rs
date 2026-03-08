#!/usr/bin/env sh
set -eu

if [ "$#" -ne 1 ]; then
  echo "usage: $0 <source-path>" >&2
  exit 1
fi

: "${LADY_LIBRARY:=./ladies/stdlib}"

SOURCE_PATH="$1"
NAME="$(basename -- "$SOURCE_PATH")"

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
BUILD_DIR="$ROOT_DIR/build/$NAME"
SCHEME_DIR="$ROOT_DIR/scheme"

RUNTIME_SLS="$SCHEME_DIR/runtime.sls"
STARTUP_SS="$SCHEME_DIR/startup.ss"
ROOT_SS="$BUILD_DIR/root.ss"
ROOT_BOOT="$BUILD_DIR/root.boot"
RUN_SH="$BUILD_DIR/run.sh"

CHEZ_PREFIX="/usr/local/lib/csv10.4.0-pre-release.3"
TARM_PREFIX="$CHEZ_PREFIX/tarm64osx"
SCHEME_BIN="$TARM_PREFIX/scheme"
PETITE_BIN="$TARM_PREFIX/petite"
PETITE_BOOT="$TARM_PREFIX/petite.boot"

if [ ! -f "$RUNTIME_SLS" ]; then
  echo "missing runtime library: $RUNTIME_SLS" >&2
  exit 1
fi

if [ ! -f "$STARTUP_SS" ]; then
  echo "missing startup file: $STARTUP_SS" >&2
  exit 1
fi

if [ -z "$PETITE_BOOT" ]; then
  echo "could not find petite.boot under $CHEZ_PREFIX/lib" >&2
  exit 1
fi

mkdir -p "$BUILD_DIR"

cargo run --bin mc -- \
  --library "$LADY_LIBRARY" \
  --source "$SOURCE_PATH" \
  --scheme "$ROOT_SS"

if [ ! -f "$ROOT_SS" ]; then
  echo "host compiler did not produce: $ROOT_SS" >&2
  exit 1
fi

"$SCHEME_BIN" -q <<EOF
(import (chezscheme))

(library-directories
  '(("$ROOT_DIR" . "$ROOT_DIR")
    ("$SCHEME_DIR" . "$SCHEME_DIR")
    ("$BUILD_DIR" . "$BUILD_DIR")))

(parameterize ([optimize-level 3])
  (compile-library "$RUNTIME_SLS")
  (compile-file "$ROOT_SS")
  (compile-file "$STARTUP_SS")
  (make-boot-file "$ROOT_BOOT"
                  '("petite" "scheme")
                  "$SCHEME_DIR/runtime.so"
                  "$BUILD_DIR/root.so"
                  "$ROOT_DIR/scheme/startup.so"))
EOF

cat > "$RUN_SH" <<EOF
#!/usr/bin/env sh
set -eu

HERE="\$(CDPATH= cd -- "\$(dirname -- "\$0")" && pwd)"
PETITE_BIN="$PETITE_BIN"
PETITE_BOOT="$PETITE_BOOT"
ROOT_BOOT="\$HERE/root.boot"

export SCHEMEHEAPDIRS="\$(dirname -- "$PETITE_BOOT"):"

exec "\$PETITE_BIN" -b "\$PETITE_BOOT" -b "\$ROOT_BOOT" "\$@"
EOF

chmod +x "$RUN_SH"

echo "built:"
echo "  $ROOT_BOOT"
echo "  $RUN_SH"
