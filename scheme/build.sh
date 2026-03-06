PREFIX="$(brew --prefix chezscheme)"
BOOTDIR="$PREFIX/lib/csv10.3.0/tarm64osx"
BINDIR="$PREFIX/bin"

chez -q <<'EOF'
(import (chezscheme))
(compile-program "first.ss")
(make-boot-file "first.boot" '("petite") "first.so")
EOF

cp first.boot "$BOOTDIR/first.boot"
ln -sf "$BINDIR/petite" ./first
