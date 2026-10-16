#!/bin/bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
TOOLCHAIN=${LEAN_TOOLCHAIN:?Set LEAN_TOOLCHAIN}
PACKAGES=${LEAN_PACKAGES:?Set LEAN_PACKAGES}
LIBPATH="$ROOT/.lake/build/lib/lean"
for pkg in "$PACKAGES"/*; do LIBPATH="$LIBPATH:$pkg/.lake/build/lib/lean"; done
export LEAN_PATH="$LIBPATH"
cd "$ROOT"
if [[ "$1" == "--lake" ]]; then shift; "$TOOLCHAIN/bin/lake" "$@"; else
  src=$1; shift
  out=".lake/build/lib/lean/${src%.lean}.olean"
  mkdir -p "$(dirname "$out")"
  "$TOOLCHAIN/bin/lean" -M 4096 -o "$out" "$src" "$@"
fi
