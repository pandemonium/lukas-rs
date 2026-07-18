#!/usr/bin/env sh
set -eu

usage() {
  echo "usage: $0 <source-directory> [--backend scheme|native]" >&2
  exit 1
}

# One positional source directory, plus an optional backend.
BACKEND=scheme
SOURCE_PATH=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --backend)
      [ "$#" -ge 2 ] || usage
      BACKEND=$2
      shift 2
      ;;
    --backend=*)
      BACKEND=${1#--backend=}
      shift
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage
      ;;
    *)
      [ -z "$SOURCE_PATH" ] || usage
      SOURCE_PATH=$1
      shift
      ;;
  esac
done

[ -n "$SOURCE_PATH" ] || usage
[ -d "$SOURCE_PATH" ] || {
  echo "source directory does not exist: $SOURCE_PATH" >&2
  exit 1
}

SOURCE_PATH="$(CDPATH= cd -- "$SOURCE_PATH" && pwd)"
[ -f "$SOURCE_PATH/Root.lady" ] || {
  echo "missing source file: $SOURCE_PATH/Root.lady" >&2
  exit 1
}

NAME="$(basename -- "$SOURCE_PATH")"
ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
BUILD_DIR="$ROOT_DIR/build/$NAME"
SCHEME_DIR="$ROOT_DIR/scheme"
C_DIR="$ROOT_DIR/c"
: "${LADY_LIBRARY:=$ROOT_DIR/ladies/stdlib}"

mkdir -p "$BUILD_DIR"
cd "$ROOT_DIR"

# Build the host compiler once up front, as c_panel.sh does.
cargo build -q --bin mc 2>/dev/null || {
  echo "build failed" >&2
  exit 1
}

case "$BACKEND" in
native)
  # Emit C and link it with the runtime and any companion C files implementing
  # foreign declarations in the source directory.
  ROOT_C="$BUILD_DIR/root.c"
  BIN="$SOURCE_PATH/$NAME"

  cargo run -q --bin mc -- \
    --library "$LADY_LIBRARY" \
    --source "$SOURCE_PATH" \
    --backend native \
    -o "$ROOT_C"

  if [ ! -s "$ROOT_C" ]; then
    echo "host compiler did not produce C: $ROOT_C" >&2
    exit 1
  fi

  # Build the clang input list without losing quoting on pathnames.
  set -- "$C_DIR/runtime.c" "$C_DIR/gc.c"
  for foreign_c in "$SOURCE_PATH"/*.c; do
    [ -e "$foreign_c" ] && set -- "$@" "$foreign_c"
  done
  set -- "$@" "$ROOT_C"

  clang -std=c11 -I"$C_DIR" -O2 -o "$BIN" "$@"

  echo "built:"
  echo "  $BIN"
  ;;

scheme)
  # Emit Scheme, compile it with Chez into a boot file, and write a run.sh
  # wrapper next to it under build/<name>/.
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

  if [ ! -f "$PETITE_BOOT" ]; then
    echo "missing petite.boot: $PETITE_BOOT" >&2
    exit 1
  fi

  cargo run -q --bin mc -- \
    --library "$LADY_LIBRARY" \
    --source "$SOURCE_PATH" \
    -o "$ROOT_SS"

  if [ ! -s "$ROOT_SS" ]; then
    echo "host compiler did not produce Scheme: $ROOT_SS" >&2
    exit 1
  fi

  "$SCHEME_BIN" -q <<EOF_SCHEME
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
EOF_SCHEME

  cat > "$RUN_SH" <<EOF_RUN
#!/usr/bin/env sh
set -eu

HERE="\$(CDPATH= cd -- "\$(dirname -- "\$0")" && pwd)"
PETITE_BIN="$PETITE_BIN"
PETITE_BOOT="$PETITE_BOOT"
ROOT_BOOT="\$HERE/root.boot"

export SCHEMEHEAPDIRS="\$(dirname -- "$PETITE_BOOT"):"

exec "\$PETITE_BIN" -b "\$PETITE_BOOT" -b "\$ROOT_BOOT" "\$@"
EOF_RUN

  chmod +x "$RUN_SH"

  echo "built:"
  echo "  $ROOT_BOOT"
  echo "  $RUN_SH"
  ;;

*)
  echo "unknown backend: $BACKEND (expected 'scheme' or 'native')" >&2
  exit 1
  ;;
esac
