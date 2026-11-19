#!/bin/sh
# Compile the SystemVerilog designs in CircuitHdlTest/Fifo/Verilog to the `hw` MLIR that
# CircuitHdlTest/Fifo/Verilog.lean reads, and check the result against what is checked in.
#
# The sibling of `scripts/firrtl.sh`, and the same bargain: the `.mlir` files are build products,
# committed because `lake test` has to work against a bare toolchain, and therefore capable of
# going stale. Editing a `.sv` without regenerating leaves Lean checking the previous circuit and
# nothing in `lake test` would notice. Run this after touching any `.sv`.
#
# Unlike `firrtl.sh` this needs a compiler the host cannot run. `circt-verilog` is built on slang
# and appears only in CIRCT releases from 1.123.0 on, which require glibc 2.36 and libstdc++ from
# GCC 13; this host is Ubuntu 22.04 with 2.35 and 3.4.30. Releases old enough to run here were
# built without slang and contain no `circt-verilog` at all -- measured on 1.113.0 and 1.122.0.
# So the compiler runs in the devcontainer, which exists for exactly this reason.
#
# Usage:  scripts/verilog.sh            diff the checked-in MLIR against freshly compiled MLIR
#         scripts/verilog.sh --update   overwrite the checked-in MLIR instead
#
# Set CIRCT_VERILOG to a `circt-verilog` that runs natively to skip Docker (that is what the
# devcontainer itself does, since CIRCT_BIN is on PATH in there).
set -eu

DIR=CircuitHdlTest/Fifo/Verilog
IMAGE="${CIRCT_IMAGE:-circuithdl-dev}"
UPDATE=""
[ "${1:-}" = "--update" ] && UPDATE=1

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Two ways to reach the tools. Inside the container both are on PATH; outside, shell into the
# image. `circt-opt` has to come from the same place as `circt-verilog` -- the host's 1.113.0
# cannot print generic form for operations a 1.164.0 frontend emits.
if [ -n "${CIRCT_VERILOG:-}" ] || command -v circt-verilog >/dev/null 2>&1; then
  CV="${CIRCT_VERILOG:-circt-verilog}"
  run_cv() { "$CV" "$@"; }
  run_opt() { circt-opt "$@"; }
  SVDIR="$DIR"
else
  command -v docker >/dev/null 2>&1 || {
    echo "no circt-verilog on PATH and no docker; see .devcontainer/README.md" >&2; exit 2; }
  docker image inspect "$IMAGE" >/dev/null 2>&1 || {
    echo "docker image '$IMAGE' not built; run:" >&2
    echo "  docker build -f .devcontainer/Dockerfile -t $IMAGE .devcontainer" >&2; exit 2; }
  # The source directory is mounted rather than piped: `circt-verilog` detects its input format
  # from the file extension and refuses stdin with "cannot auto-detect input format".
  run_cv() { docker run --rm -i -v "$PWD/$DIR:/sv:ro" "$IMAGE" circt-verilog "$@"; }
  run_opt() { docker run --rm -i "$IMAGE" circt-opt "$@"; }
  SVDIR=/sv
fi

fail=0
ran=0
for sv in "$DIR"/*.sv; do
  base=$(basename "$sv" .sv)
  ran=$((ran + 1))

  # `--ir-hw` runs the MooreToCore conversion and stops at `hw`/`comb`/`seq`, which is the level
  # `Veir.Netlist` interprets.
  #
  # `--infer-clock-ports=false` is the one that matters. Left on, the frontend retypes the clock
  # port to `!seq.clock`, and `Veir.Netlist` refuses a clock that is not a `seq.to_clock` of a
  # block argument -- a real CIRCT form it does not model. Off, the port stays `i1` with an
  # explicit `seq.to_clock`, which is the shape the lowering here also produces.
  run_cv --ir-hw --infer-clock-ports=false "$SVDIR/$base.sv" > "$tmp/$base.hw" 2>"$tmp/$base.err" || {
    echo "FAIL $base: circt-verilog exited non-zero"; sed 's/^/    /' < "$tmp/$base.err"
    fail=$((fail + 1)); continue; }

  # The same two normalisations `firrtl.sh` applies, and for the same reasons: VeIR's parser reads
  # generic MLIR only, and its property tables reject the `twoState` unit attribute outright rather
  # than ignoring it. `twoState` asserts an operand is never X or Z, which constrains the
  # environment rather than describing a computation, and `Veir.Netlist` has no X. There is no
  # `om.class` to strip here -- that is a firtool habit, not a circt-verilog one.
  run_opt --mlir-print-op-generic < "$tmp/$base.hw" \
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
    echo "FAIL $base: the checked-in MLIR is not what circt-verilog produces from $sv"
    head -30 "$tmp/$base.diff" | sed 's/^/    /'
    fail=$((fail + 1))
  fi
done

[ "$ran" -gt 0 ] || { echo "no .sv files under $DIR" >&2; exit 2; }
if [ "$fail" -ne 0 ]; then
  echo "$fail of $ran design(s) stale" >&2
  exit 1
fi
[ -n "$UPDATE" ] || echo "all $ran design(s) current"
