#!/bin/sh
# Compile the FIRRTL designs in CircuitHdlTest/Fifo/Firrtl to the `hw` MLIR that
# CircuitHdlTest/Fifo/Firrtl.lean reads, and check the result against what is checked in.
#
# The `.mlir` files are build products of `firtool`, committed because `lake test` has to keep
# working against a bare toolchain -- the package may not depend on a CIRCT install to build.
# That makes them capable of going stale: editing a `.fir` without regenerating leaves the Lean
# side checking the previous circuit, and nothing in `lake test` would notice. This script is
# what notices, so run it after touching any `.fir`.
#
# Usage:  scripts/firrtl.sh            diff the checked-in MLIR against freshly compiled MLIR
#         scripts/firrtl.sh --update   overwrite the checked-in MLIR instead
set -eu

CIRCT_BIN="${CIRCT_BIN:-/proj/xsjhdstaff2/stephenn/tools/circt-1.113.0/firtool-1.113.0/bin}"
FIRTOOL="$CIRCT_BIN/firtool"
CIRCT_OPT="$CIRCT_BIN/circt-opt"
DIR=CircuitHdlTest/Fifo/Firrtl
UPDATE=""
[ "${1:-}" = "--update" ] && UPDATE=1

[ -x "$FIRTOOL" ] || { echo "no firtool at $FIRTOOL; set CIRCT_BIN" >&2; exit 2; }
[ -x "$CIRCT_OPT" ] || { echo "no circt-opt at $CIRCT_OPT; set CIRCT_BIN" >&2; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail=0
ran=0
for fir in "$DIR"/*.fir; do
  base=$(basename "$fir" .fir)
  ran=$((ran + 1))

  # `--ir-hw` stops the pipeline at `hw`/`comb`/`seq`, which is the level Veir.Netlist
  # interprets; going further would lower registers into `sv` and leave nothing to simulate.
  "$FIRTOOL" --format=fir --ir-hw --strip-debug-info --disable-all-randomization \
    "$fir" -o "$tmp/$base.raw"

  # Three normalisations, none of which touch a circuit:
  #
  #  1. Drop the `om.class` firtool emits beside every module. It carries object-model metadata,
  #     holds no hardware, and `om` is a dialect VeIR does not register.
  #  2. Print in generic form. VeIR's parser reads generic MLIR only -- the pretty forms of
  #     `hw.module` and `comb` are CIRCT-side custom assembly it does not implement.
  #  3. Strip `result_locs` with the `#loc` aliases the generic printer reintroduces for it, and
  #     the `twoState` unit attribute on `comb` operations. `twoState` is firtool's assertion
  #     that an operand is never X or Z; it constrains the environment rather than describing a
  #     computation, and `Veir.Netlist` has no X to begin with, so dropping it changes no value
  #     any simulation produces. VeIR's property tables reject unknown attributes outright,
  #     which is why it has to go rather than being ignored.
  awk '/^  om\.class /{skip=1} skip&&/^  }$/{skip=0;next} !skip' "$tmp/$base.raw" > "$tmp/$base.hw"
  "$CIRCT_OPT" --mlir-print-op-generic "$tmp/$base.hw" \
    | sed -e '/^#loc/d' \
          -e 's/result_locs = \[[^]]*\], //' \
          -e 's/, twoState}>/}>/' \
          -e 's/<{twoState}> //' \
    > "$tmp/$base.mlir"

  if [ -n "$UPDATE" ]; then
    cp "$tmp/$base.mlir" "$DIR/$base.mlir"
    echo "wrote $DIR/$base.mlir"
  elif [ ! -f "$DIR/$base.mlir" ]; then
    echo "FAIL $base: $DIR/$base.mlir does not exist; run with --update"
    fail=$((fail + 1))
  elif diff -u "$DIR/$base.mlir" "$tmp/$base.mlir" > "$tmp/$base.diff"; then
    echo "ok   $base ($(wc -l < "$DIR/$base.mlir" | tr -d ' ') lines)"
  else
    echo "FAIL $base: the checked-in MLIR is not what firtool produces from $fir"
    head -30 "$tmp/$base.diff" | sed 's/^/    /'
    fail=$((fail + 1))
  fi
done

[ "$ran" -gt 0 ] || { echo "no .fir files under $DIR" >&2; exit 2; }
if [ "$fail" -ne 0 ]; then
  echo "$fail of $ran design(s) stale" >&2
  exit 1
fi
[ -n "$UPDATE" ] || echo "all $ran design(s) current"
