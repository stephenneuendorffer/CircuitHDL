#!/bin/sh
# Cross-check Veir.Netlist against CIRCT's own simulator.
#
# `lake exe arccheck` writes, for each design and schedule, the MLIR this package emits with an
# `arc.sim` driver appended, and what Veir.Netlist says the output ports should be
# at every tick. This runs the MLIR through `arcilator` and compares.
#
# This is the only check in the repository whose other side was not written here. The netlist
# theorems in CircuitHdlTest/{ShiftFifo,AsyncFifo}.lean compare the lowering against this
# package's reading of the comb/seq dialects; a misreading shared by both would pass them and
# fail here.
#
# Not part of `lake test`: it needs a CIRCT install, and the package has to stay buildable against
# a bare toolchain. See AGENTS.md.
#
# Usage:  scripts/arccheck.sh            run every generated case
#         scripts/arccheck.sh pattern    only cases whose filename contains `pattern`
set -eu

CIRCT_BIN="${CIRCT_BIN:-/proj/xsjhdstaff2/stephenn/tools/circt-1.113.0/firtool-1.113.0/bin}"
ARCILATOR="$CIRCT_BIN/arcilator"
DIR=build/arc
FILTER="${1:-}"

[ -x "$ARCILATOR" ] || { echo "no arcilator at $ARCILATOR; set CIRCT_BIN" >&2; exit 2; }

lake exe arccheck

fail=0
ran=0
for mlir in "$DIR"/*.mlir; do
  case "$mlir" in *"$FILTER"*) ;; *) continue ;; esac
  base=${mlir%.mlir}
  ran=$((ran + 1))

  # arcilator prints `label = <hex>`; the expected file is decimal, so that nothing in Lean has to
  # predict its formatting. Normalise both sides to decimal before comparing.
  if ! "$ARCILATOR" --run --jit-entry=main "$mlir" > "$base.actual.raw" 2> "$base.err"; then
    echo "FAIL $base: arcilator exited non-zero"
    sed 's/^/    /' < "$base.err"
    fail=$((fail + 1))
    continue
  fi
  awk '{ printf "%s = %d\n", $1, strtonum("0x" $3) }' < "$base.actual.raw" > "$base.actual"

  if diff -u "$base.expected" "$base.actual" > "$base.diff"; then
    echo "ok   $base ($(wc -l < "$base.expected" | tr -d ' ') observations)"
    rm -f "$base.diff" "$base.err" "$base.actual.raw"
  else
    echo "FAIL $base: arcilator disagrees with Veir.Netlist"
    head -30 "$base.diff" | sed 's/^/    /'
    fail=$((fail + 1))
  fi
done

[ "$ran" -gt 0 ] || { echo "no cases matched '$FILTER'" >&2; exit 2; }
if [ "$fail" -ne 0 ]; then
  echo "$fail of $ran case(s) disagree" >&2
  exit 1
fi
echo "all $ran case(s) agree"
