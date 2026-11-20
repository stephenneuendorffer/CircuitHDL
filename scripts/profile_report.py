#!/usr/bin/env python3
"""Summarise the Firefox-profiler JSON that `-Dtrace.profiler.output` writes.

Lean's profiler emits a *trace-derived* profile rather than a sampled one: every trace node
becomes a frame and carries its own measured duration as a sample weight, so "self time" here is
exact accounting rather than a statistical estimate. Threads are the elaboration tasks, so the
sum across threads is CPU time and can exceed the wall clock of the run that produced it.

With `-Dtrace.profiler.output.pp=true` each `Elab.command` frame carries the pretty-printed
command, which is what lets a report name the declaration that cost the time rather than just
the phase.
"""

import argparse
import json
import os
import sys
from collections import defaultdict


DECL = ("theorem ", "def ", "#guard", "#eval", "example ", "instance ", "abbrev ",
        "structure ", "inductive ", "@[", "set_option ", "open ", "namespace ")


def label(name, width=110):
    """Name a frame by the declaration it is working on.

    A pp'd `Elab.command` frame holds `Elab.command: <parser kind>: <the whole command>`, doc
    comment and all, so the useful line is the first one that opens a declaration -- otherwise
    every theorem in a file reports as its own prose.
    """
    head, sep, rest = name.partition(": ")
    if not sep:
        return head
    kind, sep2, body = rest.partition(": ")
    if not sep2 or " " in kind:  # not a `class: kind: body` frame after all
        kind, body = "", rest
    lines = [ln.strip() for ln in body.splitlines() if ln.strip()]
    pick = next((ln for ln in lines if ln.startswith(DECL)), None)
    if pick is None:
        skip = ("/--", "-/", "--", "/-", "*", "|")
        pick = next((ln for ln in lines if not ln.startswith(skip)), lines[0] if lines else kind)
    out = f"{head}: {pick}"
    return out[: width - 1] + "…" if len(out) > width else out


def phase(name):
    """The trace class a frame belongs to: `Elab.command`, `Kernel`, `compiler`, ..."""
    head = name.partition(": ")[0]
    return head if head else "(root)"


class Profile:
    def __init__(self, path):
        with open(path) as f:
            d = json.load(f)
        self.threads = d["threads"]
        self.path = path

    def accumulate(self, self_by_frame, incl_by_cmd, phase_self):
        """Fold one profile's samples into the three cross-module accumulators."""
        total = 0.0
        for t in self.threads:
            names = [t["stringArray"][i] for i in t["funcTable"]["name"]]
            frame_name = [names[f] for f in t["frameTable"]["func"]]
            st = t["stackTable"]
            prefix, frame = st["prefix"], st["frame"]

            # The command a stack node sits under, inherited down the tree. A declaration whose
            # proof, kernel check or compilation was spun off runs on a worker thread rooted at
            # `Elab.async` rather than under its command, so those are owners too -- otherwise
            # every `native_decide` lands in one anonymous bucket.
            owner = [None] * st["length"]
            for i in range(st["length"]):
                p = prefix[i]
                nm = frame_name[frame[i]]
                owner[i] = (owner[p] if p is not None else None) or (
                    nm if nm.startswith(("Elab.command", "Elab.async")) else None
                )

            s = t["samples"]
            for stack, w in zip(s["stack"], s["weight"]):
                if stack is None:
                    continue
                nm = frame_name[frame[stack]]
                self_by_frame[nm] += w
                phase_self[phase(nm)] += w
                incl_by_cmd[owner[stack] or "(untraced, below threshold or import)"] += w
                total += w
        return total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("profiles", nargs="+", help="profile JSON files")
    ap.add_argument("-n", type=int, default=15, help="rows per table")
    ap.add_argument("--per-module", action="store_true", help="also break each file out")
    args = ap.parse_args()

    totals = {}
    all_self, all_cmd, all_phase = defaultdict(float), defaultdict(float), defaultdict(float)

    for p in args.profiles:
        prof = Profile(p)
        s, c, ph = defaultdict(float), defaultdict(float), defaultdict(float)
        totals[p] = prof.accumulate(s, c, ph)
        for d, a in ((s, all_self), (c, all_cmd), (ph, all_phase)):
            for k, v in d.items():
                a[k] += v
        if args.per_module:
            print(f"\n=== {os.path.basename(p)}  {totals[p]/1000:.1f}s CPU")
            for k, v in sorted(c.items(), key=lambda kv: -kv[1])[: args.n]:
                print(f"  {v/1000:7.1f}s  {label(k)}")

    print(f"\n{'='*100}\nModules by CPU time")
    grand = sum(totals.values())
    for p, v in sorted(totals.items(), key=lambda kv: -kv[1]):
        print(f"  {v/1000:8.1f}s  {100*v/grand:5.1f}%  {os.path.basename(p)[:-5]}")
    print(f"  {grand/1000:8.1f}s  total")

    print(f"\n{'='*100}\nTime by trace phase (self)")
    for k, v in sorted(all_phase.items(), key=lambda kv: -kv[1])[: args.n]:
        print(f"  {v/1000:8.1f}s  {100*v/grand:5.1f}%  {k}")

    print(f"\n{'='*100}\nTop commands across all modules (inclusive)")
    for k, v in sorted(all_cmd.items(), key=lambda kv: -kv[1])[: args.n]:
        print(f"  {v/1000:8.1f}s  {label(k)}")

    print(f"\n{'='*100}\nTop single frames (self)")
    for k, v in sorted(all_self.items(), key=lambda kv: -kv[1])[: args.n]:
        print(f"  {v/1000:8.1f}s  {label(k)}")


if __name__ == "__main__":
    sys.exit(main())
