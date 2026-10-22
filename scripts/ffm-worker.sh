#!/bin/sh
# A Lean worker as a library okay loads into its own process through FFM (`ForeignWorker.inProcess(path)`):
# the worker's module and everything it imports, compiled with ffi/okay_exchange.c, Lean's runtime linked in.
#
#   scripts/ffm-worker.sh [Module] [library]
#
# Module: a module that exports its worker, `@[export okay_lean_worker] def worker (_ : Unit) : Worker`
# (default Tests.ConformanceWorker); library: default .lake/build/lib/libokay-lean-worker.dylib (.so on Linux).
set -eu
cd "$(dirname "$0")/.."
MOD=${1:-Tests.ConformanceWorker}
case "$(uname)" in Darwin) EXT=dylib ;; *) EXT=so ;; esac
OUT=${2:-.lake/build/lib/libokay-lean-worker.$EXT}
export PATH="$HOME/.elan/bin:$PATH"

lake build "$MOD" >/dev/null
IR=.lake/build/ir
SRC="$IR/$(echo "$MOD" | tr . /).c"
# the worker module's initializer, which initializes all it imports
INIT=$(grep -o '^LEAN_EXPORT lean_object\* initialize_[A-Za-z0-9_]*' "$SRC" | sed 's/.* //' | head -1)
[ -n "$INIT" ] || { echo "no initializer in $SRC" >&2; exit 1; }
# the C of the module and of everything it imports from this package, by its import lines
closure() {
  todo=$1; seen=""
  while [ -n "$todo" ]; do
    m=${todo%% *}; [ "$todo" = "$m" ] && todo="" || todo=${todo#* }
    case " $seen " in *" $m "*) continue ;; esac
    f="$(echo "$m" | tr . /).lean"
    [ -f "$f" ] || continue
    seen="$seen $m"
    for i in $(sed -n 's/^import  *\([A-Za-z0-9_.]*\).*/\1/p' "$f"); do todo="$todo $i"; done
    todo=${todo# }
  done
  for m in $seen; do echo "$IR/$(echo "$m" | tr . /).c"; done
}
CS=$(closure "$MOD")
OBJ=.lake/build/ffi
mkdir -p "$(dirname "$OUT")" "$OBJ"
PREFIX=$(lean --print-prefix)
# Lean's C by leanc (its headers and flags), position-independent; on macOS for the system's own version, which
# the linker below targets (leanc's own target says 99.0)
case "$(uname)" in Darwin) MIN="-mmacosx-version-min=$(sw_vers -productVersion)" ;; *) MIN="" ;; esac
OS=""
for c in $CS; do
  o="$OBJ/$(echo "${c#$IR/}" | tr / _ | sed 's/\.c$/.o/')"
  leanc -c -fPIC -O3 -DNDEBUG $MIN -o "$o" "$c"
  OS="$OS $o"
done
# the shim by the system's compiler (it needs pthread.h), with Lean's header
cc -c -fPIC -O2 $MIN -I"$PREFIX/include" -DOKAY_LEAN_INIT="$INIT" -o "$OBJ/okay_exchange.o" ffi/okay_exchange.c
# one library, Lean's runtime in it — as a Lean executable links it, not leanc -shared's @rpath libLake_shared:
# a JVM loads it from its path alone
case "$(uname)" in Darwin) STRIP=-Wl,-dead_strip ;; *) STRIP=-Wl,--gc-sections ;; esac
cc -shared $MIN -o "$OUT" $OS "$OBJ/okay_exchange.o" -L"$PREFIX/lib/lean" -L"$PREFIX/lib" \
  -lleancpp -lInit -lStd -lleanrt -lc++ -lgmp -luv -lpthread $STRIP
echo "$OUT"
