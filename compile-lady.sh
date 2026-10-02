#!/usr/bin/env sh
set -eu

usage() {
  cat >&2 <<USAGE
usage: $0 [--backend native|scheme] [--profile <target>] <source-directory>

Compiles a Marmelade/Lady source directory containing Root.lady.

Options:
  --backend native   Generate C and link a native executable (default)
  --backend scheme   Generate Scheme and build a Chez Scheme boot file
  --profile host            Build a process for the current host (default)
  --profile native-macos    Build a macOS process
  --profile native-linux    Build a Linux process
  --profile native-windows  Build a Windows process
  --profile wasm-node       Build an ES module and Wasm binary for Node
  --profile wasm-browser    Build an ES module and Wasm binary for a browser
  -h, --help         Show this help

Environment:
  LADY_LIBRARY       Standard-library directory
  CC                 C compiler for the native backend (default: clang)
  CFLAGS             Additional native compiler flags (default: -O2)
  EMCC               Emscripten compiler for Wasm profiles (default: emcc)
  EM_CACHE           Emscripten cache (default: build/emscripten-cache)
  WASM_CFLAGS        Additional Emscripten flags (default: -O2 -flto)
  LADY_CAPABILITIES  Provider model (default: <library>/capabilities.conf)
  SCHEME_BIN         Chez Scheme executable for the Scheme backend
  PETITE_BIN         Chez Petite executable for the Scheme backend
  PETITE_BOOT        Path to petite.boot for the Scheme backend
USAGE
  exit "${1:-1}"
}

die() {
  echo "compile-lady.sh: $*" >&2
  exit 1
}

shell_quote() {
  # Print one string as a single-quoted POSIX shell word.
  printf "'"
  printf '%s' "$1" | sed "s/'/'\\\\''/g"
  printf "'"
}

BACKEND="${LADY_BACKEND:-native}"
PROFILE="${LADY_PROFILE:-host}"
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
    --profile)
      [ "$#" -ge 2 ] || usage
      PROFILE=$2
      shift 2
      ;;
    --profile=*)
      PROFILE=${1#--profile=}
      shift
      ;;
    -h|--help)
      usage 0
      ;;
    -*)
      die "unknown option: $1"
      ;;
    *)
      [ -z "$SOURCE_PATH" ] || die "only one source directory may be supplied"
      SOURCE_PATH=$1
      shift
      ;;
  esac
done

[ -n "$SOURCE_PATH" ] || usage

# Compatibility with the original two-profile spelling.
[ "$PROFILE" = browser ] && PROFILE=wasm-browser

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

# Support keeping this script either in the repository root or in its c/
# directory. MARMELADE_ROOT can be used for any other layout.
if [ -n "${MARMELADE_ROOT:-}" ]; then
  ROOT_DIR=$(CDPATH= cd -- "$MARMELADE_ROOT" && pwd) \
    || die "cannot open MARMELADE_ROOT: $MARMELADE_ROOT"
elif [ -f "$SCRIPT_DIR/Cargo.toml" ] && [ -d "$SCRIPT_DIR/c" ]; then
  ROOT_DIR=$SCRIPT_DIR
elif [ -f "$SCRIPT_DIR/../Cargo.toml" ] && [ -d "$SCRIPT_DIR/../c" ]; then
  ROOT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
else
  die "cannot locate the repository root; set MARMELADE_ROOT"
fi

[ -d "$SOURCE_PATH" ] || die "source directory does not exist: $SOURCE_PATH"
SOURCE_PATH=$(CDPATH= cd -- "$SOURCE_PATH" && pwd)

[ -f "$SOURCE_PATH/Root.lady" ] \
  || die "missing source file: $SOURCE_PATH/Root.lady"

NAME=$(basename -- "$SOURCE_PATH")
BUILD_DIR="$ROOT_DIR/build/$NAME"
SCHEME_DIR="$ROOT_DIR/scheme"
C_DIR="$ROOT_DIR/c"
LADY_LIBRARY=${LADY_LIBRARY:-"$ROOT_DIR/ladies/stdlib"}

[ -d "$LADY_LIBRARY" ] || die "library directory does not exist: $LADY_LIBRARY"
LADY_LIBRARY=$(CDPATH= cd -- "$LADY_LIBRARY" && pwd)

[ -f "$ROOT_DIR/Cargo.toml" ] || die "missing Cargo.toml under $ROOT_DIR"
[ -f "$C_DIR/runtime.c" ] || die "missing native runtime: $C_DIR/runtime.c"
[ -f "$C_DIR/gc.c" ] || die "missing garbage collector: $C_DIR/gc.c"

mkdir -p "$BUILD_DIR"
cd "$ROOT_DIR"

run_mc() {
  cargo run --release -q --bin mc -- "$@"
}

case "$BACKEND" in
  native)
    CAPABILITY_MODEL=${LADY_CAPABILITIES:-"$LADY_LIBRARY/capabilities.conf"}
    [ -f "$CAPABILITY_MODEL" ] || die "capability model does not exist: $CAPABILITY_MODEL"
    CAPABILITY_MODEL=$(CDPATH= cd -- "$(dirname -- "$CAPABILITY_MODEL")" && pwd)/$(basename -- "$CAPABILITY_MODEL")

    case "$PROFILE" in
      host|native-macos|native-linux|native-windows|wasm-node|wasm-browser) ;;
      *) die "unknown native profile: $PROFILE" ;;
    esac

    if [ "$PROFILE" = wasm-browser ] || [ "$PROFILE" = wasm-node ]; then
      if [ "$PROFILE" = wasm-browser ]; then
        WASM_DIR="$BUILD_DIR/browser"
      else
        WASM_DIR="$BUILD_DIR/node"
      fi
      mkdir -p "$WASM_DIR"
      ROOT_C="$WASM_DIR/root.generated.c"
    else
    # Keep generated C beside Root.lady. The leading dot prevents the ordinary
    # "$SOURCE_PATH"/*.c glob below from treating it as a foreign implementation.
      ROOT_C="$SOURCE_PATH/.${NAME}.generated.c"
    fi
    # A fixed name, so one .gitignore rule covers every program's binary rather
    # than one rule per directory name.
    if [ "$PROFILE" = host ]; then
      BIN="$SOURCE_PATH/exe"
    else
      mkdir -p "$BUILD_DIR/$PROFILE"
      BIN="$BUILD_DIR/$PROFILE/exe"
    fi
    C_SOURCE_LIST="$BUILD_DIR/native-c-sources.txt"
    PROVIDER_PLAN="$BUILD_DIR/providers-$PROFILE.txt"
    REQUIREMENTS_REPORT="$BUILD_DIR/requirements-$PROFILE.txt"
    if [ "$PROFILE" != wasm-browser ] && [ "$PROFILE" != wasm-node ]; then
      cc_was_set=${CC+x}
      CC=${CC:-clang}
      # The one definition of the native flags, shared with the test panel.
      . "$C_DIR/cflags.sh"
      command -v "$CC" >/dev/null 2>&1 \
        || die "C compiler not found: $CC"
      host_target=unknown
      case "$(uname -s)" in
        Darwin) host_target=native-macos ;;
        Linux) host_target=native-linux ;;
        MINGW*|MSYS*|CYGWIN*|Windows_NT) host_target=native-windows ;;
      esac
      if [ "$PROFILE" != host ] && [ "$PROFILE" != "$host_target" ] && [ -z "$cc_was_set" ]; then
        die "$PROFILE is a cross target on this machine; set CC to an appropriate cross compiler"
      fi
    fi

    rm -f "$ROOT_C" "$PROVIDER_PLAN" "$REQUIREMENTS_REPORT"

    if ! run_mc \
      --library "$LADY_LIBRARY" \
      --source "$SOURCE_PATH" \
      --backend native \
      --profile "$PROFILE" \
      --capabilities "$CAPABILITY_MODEL" \
      --provider-plan "$PROVIDER_PLAN" \
      --requirements-report "$REQUIREMENTS_REPORT" \
      -o "$ROOT_C"; then
      die "the host compiler failed while generating C"
    fi

    [ -s "$ROOT_C" ] || die "the host compiler did not produce C: $ROOT_C"

    # Collect companion C implementations from both the source module and the
    # complete standard-library tree. Provider-owned sources are omitted below
    # and only the selected ones are added back from the provider plan.
    : > "$C_SOURCE_LIST"

    for foreign_c in "$SOURCE_PATH"/*.c; do
      [ -e "$foreign_c" ] && printf '%s\n' "$foreign_c" >> "$C_SOURCE_LIST"
    done

    find "$LADY_LIBRARY" -type f -name '*.c' -print >> "$C_SOURCE_LIST"

    set -- "$C_DIR/runtime.c" "$C_DIR/gc.c"
    while IFS= read -r foreign_c || [ -n "$foreign_c" ]; do
      if [ -n "$foreign_c" ]; then
        if grep -Fqx "managed-source $foreign_c" "$PROVIDER_PLAN"; then
          continue
        fi
        if { [ "$PROFILE" = wasm-browser ] || [ "$PROFILE" = wasm-node ]; } \
          && [ "${foreign_c#"$LADY_LIBRARY"/}" != "$foreign_c" ]; then
          relative=${foreign_c#"$LADY_LIBRARY"/}
          module=${relative%.c}
          mangled=$(printf '%s' "$module" | tr '/.' '__')
          prefix="Root_${mangled}_"
          if ! grep -q "$prefix" "$ROOT_C"; then
            continue
          fi
        fi
        set -- "$@" "$foreign_c"
      fi
    done < "$C_SOURCE_LIST"
    set -- "$@" "$ROOT_C"

    while IFS=' ' read -r kind value || [ -n "$kind" ]; do
      case "$kind" in
        define) set -- "$@" "-D$value=1" ;;
        source) set -- "$@" "$value" ;;
      esac
    done < "$PROVIDER_PLAN"

    if [ "$PROFILE" = wasm-browser ] || [ "$PROFILE" = wasm-node ]; then
      EMCC=${EMCC:-emcc}
      EM_CACHE=${EM_CACHE:-"$ROOT_DIR/build/emscripten-cache"}
      export EM_CACHE
      WASM_CFLAGS=${WASM_CFLAGS:--O2 -flto}
      MODULE_JS="$WASM_DIR/marmelade.mjs"
      MODULE_WASM="$WASM_DIR/marmelade.wasm"

      command -v "$EMCC" >/dev/null 2>&1 \
        || die "Emscripten compiler not found: $EMCC"

      # WASM_CFLAGS is intentionally word-split, matching normal compiler-variable
      # behavior in build scripts.
      # shellcheck disable=SC2086
      wasm_environment=web
      [ "$PROFILE" = wasm-node ] && wasm_environment=node
      if ! "$EMCC" -std=c23 -DMARMELADE_SINGLE_THREADED=1 \
        -DMARMELADE_WASM=1 -I"$C_DIR" \
        $WASM_CFLAGS --no-entry \
        -sMODULARIZE=1 -sEXPORT_ES6=1 \
        -sEXPORT_NAME=createMarmeladeModule \
        -sEXPORTED_FUNCTIONS=_marmelade_start \
        -sENVIRONMENT="$wasm_environment" -sALLOW_MEMORY_GROWTH=1 \
        -o "$MODULE_JS" "$@"; then
        die "$PROFILE WebAssembly compilation failed"
      fi

      if [ "$PROFILE" = wasm-browser ]; then
        INDEX_HTML="$WASM_DIR/index.html"
        cat > "$INDEX_HTML" <<'EOF_HTML'
<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Marmelade</title>
<pre id="output"></pre>
<script type="module">
  import createMarmeladeModule from "./marmelade.mjs";

  const output = document.querySelector("#output");
  const write = line => output.append(`${line}\n`);
  const marmelade = await createMarmeladeModule({ print: write, printErr: write });
  marmelade._marmelade_start();
</script>
</html>
EOF_HTML
      else
        NODE_RUNNER="$WASM_DIR/run.mjs"
        cat > "$NODE_RUNNER" <<'EOF_NODE'
import createMarmeladeModule from "./marmelade.mjs";

const marmelade = await createMarmeladeModule();
marmelade._marmelade_start();
EOF_NODE
      fi

      [ -s "$MODULE_JS" ] || die "Emscripten did not produce: $MODULE_JS"
      [ -s "$MODULE_WASM" ] || die "Emscripten did not produce: $MODULE_WASM"

      echo "generated $PROFILE module:"
      echo "  $MODULE_JS"
      echo "  $MODULE_WASM"
      if [ "$PROFILE" = wasm-browser ]; then
        echo "browser entry page:"
        echo "  $INDEX_HTML"
      else
        echo "Node entry module:"
        echo "  $NODE_RUNNER"
      fi
    else
      # CFLAGS is intentionally word-split, matching normal compiler-variable
      # behavior in build scripts.
      # shellcheck disable=SC2086
      if ! "$CC" $CSTD -I"$C_DIR" $CFLAGS -o "$BIN" "$@"; then
        die "native C compilation failed"
      fi

      echo "generated C:"
      echo "  $ROOT_C"
      echo "built native executable:"
      echo "  $BIN"
    fi
    ;;

  scheme)
    [ "$PROFILE" = host ] \
      || die "the Scheme backend only supports the host profile"
    RUNTIME_SLS="$SCHEME_DIR/runtime.sls"
    STARTUP_SS="$SCHEME_DIR/startup.ss"
    ROOT_SS="$BUILD_DIR/root.ss"
    ROOT_BOOT="$BUILD_DIR/root.boot"
    RUN_SH="$BUILD_DIR/run.sh"

    [ -f "$RUNTIME_SLS" ] || die "missing runtime library: $RUNTIME_SLS"
    [ -f "$STARTUP_SS" ] || die "missing startup file: $STARTUP_SS"

    SCHEME_BIN=${SCHEME_BIN:-}
    PETITE_BIN=${PETITE_BIN:-}
    PETITE_BOOT=${PETITE_BOOT:-}

    if [ -z "$SCHEME_BIN" ]; then
      SCHEME_BIN=$(command -v scheme 2>/dev/null || true)
    fi

    if [ -z "$PETITE_BIN" ]; then
      PETITE_BIN=$(command -v petite 2>/dev/null || true)
    fi

    [ -n "$SCHEME_BIN" ] && [ -x "$SCHEME_BIN" ] \
      || die "Chez Scheme was not found; set SCHEME_BIN"
    [ -n "$PETITE_BIN" ] && [ -x "$PETITE_BIN" ] \
      || die "Chez Petite was not found; set PETITE_BIN"

    if [ -z "$PETITE_BOOT" ]; then
      petite_parent=$(CDPATH= cd -- "$(dirname -- "$PETITE_BIN")/.." && pwd)
      PETITE_BOOT=$(
        find "$petite_parent" -type f -name petite.boot -print 2>/dev/null \
          | head -n 1 || true
      )
    fi

    [ -n "$PETITE_BOOT" ] && [ -f "$PETITE_BOOT" ] \
      || die "petite.boot was not found; set PETITE_BOOT"

    rm -f "$ROOT_SS" "$ROOT_BOOT" "$BUILD_DIR/root.so"

    if ! run_mc \
      --library "$LADY_LIBRARY" \
      --source "$SOURCE_PATH" \
      --backend scheme \
      -o "$ROOT_SS"; then
      die "the host compiler failed while generating Scheme"
    fi

    [ -s "$ROOT_SS" ] || die "the host compiler did not produce Scheme: $ROOT_SS"

    export LADY_ROOT_DIR="$ROOT_DIR"
    export LADY_SCHEME_DIR="$SCHEME_DIR"
    export LADY_BUILD_DIR="$BUILD_DIR"
    export LADY_RUNTIME_SLS="$RUNTIME_SLS"
    export LADY_ROOT_SS="$ROOT_SS"
    export LADY_STARTUP_SS="$STARTUP_SS"
    export LADY_ROOT_BOOT="$ROOT_BOOT"

    if ! "$SCHEME_BIN" -q <<'EOF_SCHEME'
(import (chezscheme))

(define root-dir    (getenv "LADY_ROOT_DIR"))
(define scheme-dir  (getenv "LADY_SCHEME_DIR"))
(define build-dir   (getenv "LADY_BUILD_DIR"))
(define runtime-sls (getenv "LADY_RUNTIME_SLS"))
(define root-ss     (getenv "LADY_ROOT_SS"))
(define startup-ss  (getenv "LADY_STARTUP_SS"))
(define root-boot   (getenv "LADY_ROOT_BOOT"))

(library-directories
  (list (cons root-dir root-dir)
        (cons scheme-dir scheme-dir)
        (cons build-dir build-dir)))

(parameterize ([optimize-level 3])
  (compile-library runtime-sls)
  (compile-file root-ss)
  (compile-file startup-ss)
  (make-boot-file root-boot
                  '("petite" "scheme")
                  (string-append scheme-dir "/runtime.so")
                  (string-append build-dir "/root.so")
                  (string-append scheme-dir "/startup.so")))
EOF_SCHEME
    then
      die "Chez Scheme compilation failed"
    fi

    [ -s "$ROOT_BOOT" ] || die "Chez Scheme did not produce: $ROOT_BOOT"

    {
      echo '#!/usr/bin/env sh'
      echo 'set -eu'
      echo
      echo 'HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)'
      printf 'DEFAULT_PETITE_BIN=%s\n' "$(shell_quote "$PETITE_BIN")"
      printf 'DEFAULT_PETITE_BOOT=%s\n' "$(shell_quote "$PETITE_BOOT")"
      echo 'PETITE_BIN=${PETITE_BIN:-$DEFAULT_PETITE_BIN}'
      echo 'PETITE_BOOT=${PETITE_BOOT:-$DEFAULT_PETITE_BOOT}'
      echo 'ROOT_BOOT="$HERE/root.boot"'
      echo
      echo 'export SCHEMEHEAPDIRS="$(dirname -- "$PETITE_BOOT"):"'
      echo 'exec "$PETITE_BIN" -b "$PETITE_BOOT" -b "$ROOT_BOOT" "$@"'
    } > "$RUN_SH"

    chmod +x "$RUN_SH"

    echo "built Scheme boot image:"
    echo "  $ROOT_BOOT"
    echo "runner:"
    echo "  $RUN_SH"
    ;;

  *)
    die "unknown backend: $BACKEND (expected native or scheme)"
    ;;
esac
