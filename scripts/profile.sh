#!/usr/bin/env bash
# Time the elaboration of every module, one process per module, the way `lake build` runs them.
#
#   scripts/profile.sh                             # time every module in the package
#   scripts/profile.sh CircuitHdlTest/Mesh.lean    # just these
#   PROFILE=1 scripts/profile.sh CircuitHdl/Core.lean   # and write a trace profile per module
#
# Writes build/profile/times.tsv (module, wall, user, sys, status) and prints the slowest first.
#
# Four things this gets right that the obvious invocation does not, each of which cost time to
# find out and each of which produces a *plausible* wrong answer rather than an error:
#
# - **Every precompiled dependency is loaded.** `CircuitHdl` sets `precompileModules`, so lake
#   passes `--load-dynlib` for it and for VeIR, lean-ctrees and Coinductive beneath it. Without
#   those flags `native_decide` falls back to Lean's IR interpreter and the module still builds,
#   roughly 4x slower -- and the dynlibs must be given leaves-first, since each one's undefined
#   symbols are resolved by the ones before it.
# - **A failed build is not a fast build.** A `lean` that dies on a missing symbol exits in a
#   second or two, which times as a spectacular improvement if the only thing recorded is the
#   clock. Every row carries ok/FAILED and the log is kept.
# - `lean` is invoked directly rather than through `lake env lean`. The wrapper resolves the
#   workspace in a second process and costs about 5s per call, which a real `lake build` pays
#   once for the whole build rather than once per module.
# - The profiler is off unless PROFILE=1. It is not free: `CircuitHdlTest/RegFile.lean` was 13.8s
#   plain, 18.8s under `-Dtrace.profiler=true`, and 22.7s with `trace.profiler.output.pp` as well.
#   `pp` is left off even then -- it pretty-prints the term at every trace node, which on a module
#   full of large `native_decide` goals is not a constant factor: `Fifo/Async.lean` ran past 20
#   minutes under it against about 100s plain. Turn it on for a cheap module, where it is what
#   lets `profile_report.py` name the declaration rather than the phase.
#
# Modules run serially, so these are per-module costs and not the build's critical path -- lake
# elaborates independent modules concurrently. Wall clock on a shared host varies severalfold
# between runs (`Fifo/Shift.lean` came in at 33.0s, 11.3s and 20.1s with nothing changed between),
# so treat a single pass as a ranking and re-run anything you intend to quote.
set -euo pipefail
cd "$(dirname "$0")/.."

out=build/profile
mkdir -p "$out"

LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH
LEAN="$(lake env which lean)"

# Leaves first: a dynlib's undefined symbols are resolved by those already loaded.
dynlibs=()
for so in .lake/packages/*/.lake/build/lib/*.so \
          ../veir/*/.lake/build/lib/*.so ../veir/.lake/build/lib/*.so \
          .lake/build/lib/*.so; do
  [ -f "$so" ] && dynlibs+=("--load-dynlib=$(cd "$(dirname "$so")" && pwd)/$(basename "$so")")
done

if [ $# -gt 0 ]; then
  files=("$@")
else
  mapfile -t files < <(find CircuitHdl CircuitHdlTest -name '*.lean' | sort
                       ls CircuitHdl.lean CircuitHdlTest.lean CircuitHdlQuick.lean)
fi

: > "$out/times.tsv"
for f in "${files[@]}"; do
  mod="${f%.lean}"; mod="${mod//\//.}"
  opts=()
  [ -n "${PROFILE:-}" ] && opts=(-Dtrace.profiler=true -Dtrace.profiler.output="$out/$mod.json"
                                 ${PP:+-Dtrace.profiler.output.pp=true})
  status=ok
  /usr/bin/time -f "%e\t%U\t%S" -o "$out/$mod.time" \
    "$LEAN" "${dynlibs[@]}" "${opts[@]}" "$f" > "$out/$mod.log" 2>&1 || status=FAILED
  # An error Lean reports on stdout still exits non-zero, but check the log too: a module that
  # elaborates while printing errors is not a module that passed.
  grep -qE '^[^ ]*error' "$out/$mod.log" && status=FAILED
  # On failure `/usr/bin/time` prefixes its output file with "Command exited with ...", so take
  # the last line rather than the whole file or the row comes out mangled.
  printf '%s\t%s\t%s\n' "$mod" "$(tail -1 "$out/$mod.time")" "$status" >> "$out/times.tsv"
  tail -1 "$out/times.tsv"
done

echo
printf '%-45s %8s %8s %8s  %s\n' MODULE WALL USER SYS STATUS
sort -t$'\t' -k2 -rn "$out/times.tsv" |
  awk -F'\t' '{printf "%-45s %8.1f %8.1f %8.1f  %s\n",$1,$2,$3,$4,$5}'
grep -q FAILED "$out/times.tsv" && echo && echo "FAILED rows above: see build/profile/<module>.log"
exit 0
