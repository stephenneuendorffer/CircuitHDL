import CircuitHdl

/-!
Tests for the combinational settle order.

`CircuitHdl.SettleOrder` exists because `Module.settle` makes one pass and the lowering emits one
straight-line body, so both are only correct if a statement follows the statements that drive it.
Three things need checking, and they are different in kind:

1. the order is **computed**, not assumed -- a module written back to front settles correctly;
2. the order is **stable** -- a module already in dependency order is left exactly as it was, which
   is what lets every pre-existing theorem in this package keep its old value;
3. a genuine combinational **loop is reported** rather than silently miscompiled, which is the
   failure that motivated the file.

The third is the one with teeth. Before this existed, a loop was not an error anywhere: the
evaluator read a stale value and the lowering emitted a constant zero, and those two disagree, so
a design could pass its refinement theorems and lower to something that does not work.
-/

namespace CircuitHdl

open Lean

/-! ### What two accesses share

The scheduler asks whether one statement's write can reach another statement's read. For scalars
that is name equality; for arrays it is not, because a dynamically indexed write touches every
element without being equal to any of them.

Each line below is a pair the scheduler will get wrong if `Signal.overlaps` is weakened, and the
negative ones matter as much: an array that overlapped itself at every index would put two
statements driving different elements in a cycle, which is the failure `SettleOrder` exists to
prevent one level up.
-/

#guard Signal.overlaps (.sig `a) (.sig `a)
#guard !Signal.overlaps (.sig `a) (.sig `b)
-- Two elements meet only at the same index. This is the line that keeps an array schedulable.
#guard Signal.overlaps (.elem `a 3) (.elem `a 3)
#guard !Signal.overlaps (.elem `a 3) (.elem `a 2)
#guard !Signal.overlaps (.elem `a 3) (.elem `b 3)
-- A dynamic access is every element, so it meets each of them, in both directions.
#guard Signal.overlaps (.whole `a) (.elem `a 3)
#guard Signal.overlaps (.elem `a 0) (.whole `a)
#guard Signal.overlaps (.whole `a) (.whole `a)
#guard !Signal.overlaps (.whole `a) (.elem `b 0)
-- A name is either an array or it is not, so these never meet whatever the index.
#guard !Signal.overlaps (.sig `a) (.elem `a 0)
#guard !Signal.overlaps (.sig `a) (.whole `a)

/-! ### A module written back to front

`b` reads `a`, and is written first. Under source order `b` would see `a`'s pre-pass value, which
is zero out of `initState`; under a dependency order it sees `x + 1`.
-/

private def reversed : Module :=
  Module.ofItems `reversed [(`x, 4)] [(`b, 4)]
    [ Item.reg `a 4,
      Item.stmt (.assign `b (.bin .add 4 (.var `a) (.lit 4 1))),
      Item.stmt (.assign `a (.bin .add 4 (.var `x) (.lit 4 1))) ]

private def w4 (n : Nat) : Cell := .sig (Value.ofNat 4 n)
private def w8 (n : Nat) : Cell := .sig (Value.ofNat 8 n)
private def w2 (n : Nat) : Cell := .sig (Value.ofNat 2 n)

private def settledAt (m : Module) (ins : State) (probe : Name) : Option Nat :=
  match m.settle (m.initState.apply ins) with
  | .ok σ => σ.valueOf? probe
  | .error _ => none

-- x = 5 gives a = 6 and b = 7, in one pass, despite `b` being written first.
#guard settledAt reversed [(`x, w4 5)] `a = some 6
#guard settledAt reversed [(`x, w4 5)] `b = some 7

-- And the statements really were reordered, rather than the right answer arriving by luck.
#guard reversed.settleOrder.steps.map Stmt.targets = [[.sig `a], [.sig `b]]
#guard reversed.settleOrder.unresolved = []

/-! ### Stability

A module already in dependency order must come back untouched: the schedule is a `foldl` over
`Module.settle` either way, so any reshuffling here would change the value of every `native_decide`
refinement theorem in the package. The tie-break in `SettleOrder.of` takes the lowest-numbered
ready statement for exactly this reason.
-/

private def forward : Module :=
  Module.ofItems `forward [(`x, 4)] [(`b, 4)]
    [ Item.reg `a 4,
      Item.stmt (.assign `a (.bin .add 4 (.var `x) (.lit 4 1))),
      Item.stmt (.assign `b (.bin .add 4 (.var `a) (.lit 4 1))) ]

#guard forward.settleOrder.steps.map Stmt.targets = [[.sig `a], [.sig `b]]
#guard settledAt forward [(`x, w4 5)] `b = some 7

-- The real designs are all in this case, which is why reordering them changes nothing.
#guard (asyncFifo 4 8 (by decide)).settleOrder.unresolved = []
#guard (shiftFifo 4 8).settleOrder.unresolved = []
#guard (pipeFifo4 8).settleOrder.unresolved = []

/-! ### A signal that reads itself is not a loop

`a = a | x` reads the value from before the pass, the way a blocking assignment in a settled
netlist does. Counting that as a dependency would make every accumulator unschedulable, so
`SettleOrder.of` excludes a statement's own writes from what it waits on.
-/

private def selfRead : Module :=
  Module.ofItems `selfRead [(`x, 4)] [(`a, 4)]
    [ Item.stmt (.assign `a (.bin .or 4 (.var `a) (.var `x))) ]

#guard selfRead.settleOrder.unresolved = []
#guard settledAt selfRead [(`x, w4 5)] `a = some 5

/-! ### The negative control: a real loop is reported

Two statements each reading what the other writes. There is no order, and `unresolved` names both
signals rather than the function quietly picking one. This is the shape the mesh had before the
switch was given registered ports -- A's output a combinational function of B's, and B's of A's --
only spread over sixteen instances and 672 signals instead of two.
-/

private def loopy : Module :=
  Module.ofItems `loopy [] [(`p, 1)]
    [ Item.reg `q 1,
      Item.stmt (.assign `p (.var `q)),
      Item.stmt (.assign `q (.var `p)) ]

#guard loopy.settleOrder.unresolved.length = 2
#guard loopy.settleOrder.unresolved.contains (.sig `p)
#guard loopy.settleOrder.unresolved.contains (.sig `q)
-- Nothing is dropped: a design with a loop still settles, to whatever the stale reads give, which
-- is what it did before this file existed.
#guard loopy.settleOrder.steps.length = 2

-- A loop through three statements is found too, so the check is not special-cased to a pair.
private def loopy3 : Module :=
  Module.ofItems `loopy3 [] [(`p, 1)]
    [ Item.reg `q 1, Item.reg `r 1,
      Item.stmt (.assign `p (.var `r)),
      Item.stmt (.assign `q (.var `p)),
      Item.stmt (.assign `r (.var `q)) ]

#guard loopy3.settleOrder.unresolved.length = 3

-- And a module with a loop in one place still orders the rest: `s` depends on nothing in the
-- cycle and is scheduled first, so `unresolved` is about the loop and not about the module.
private def loopyPlus : Module :=
  Module.ofItems `loopyPlus [(`x, 1)] [(`p, 1)]
    [ Item.reg `q 1, Item.reg `s 1,
      Item.stmt (.assign `p (.var `q)),
      Item.stmt (.assign `q (.var `p)),
      Item.stmt (.assign `s (.var `x)) ]

#guard loopyPlus.settleOrder.unresolved.length = 2
#guard loopyPlus.settleOrder.steps.map Stmt.targets = [[.sig `s], [.sig `p], [.sig `q]]

/-! ### Arrays, where the key type earns its keep

An array is one declaration but many drivers, so the scheduler orders it element by element. The
three modules below are what that buys, and each was checked by breaking `Signal.overlaps` so that
two elements of one array always overlap -- the whole-array granularity an array would have if it
were a single vertex.

What that mutation does is worth recording, because it is **not** a reported loop:

- `crossed` comes back ordered `a[1], o, a[0]` -- a schedule in which `a[1]` reads `a[0]` before
  anything drives it -- and settles to `[42, 0]` with `o = 0` rather than `[42, 42]` and `42`;
- `arrLoop`, which has a real cycle, comes back with `unresolved = []`.

So the granularity is load-bearing in both directions at once: too coarse and correct designs
silently read stale values, while the loop detector stops seeing the loops it is for.
-/

/-- Two statements driving different elements of one array, each reading the other's. There is an
order -- `a[0]` then `a[1]` -- and finding it is the whole point. -/
private def crossed : Module :=
  Module.ofItems `crossed [(`x, 8)] [(`o, 8)]
    [ Item.array `a 2 8,
      Item.stmt (.assign `o (.elem `a 8 1)),
      Item.stmt (.setElem `a 8 1 (.elem `a 8 0)),
      Item.stmt (.setElem `a 8 0 (.var `x)) ]

#guard crossed.settleOrder.unresolved = []
#guard crossed.settleOrder.steps.map Stmt.targets
  = [[.elem `a 0], [.elem `a 1], [.sig `o]]
-- Both elements take `x`, and the output sees it in the same pass.
#guard (crossed.settle (crossed.initState.apply [(`x, w8 42)])).toOption.bind
  (State.memOf? · `a) = some [42, 42]

/-- A dynamic write touches every element, so a static read of one of them waits for it. -/
private def dynOrder : Module :=
  Module.ofItems `dynOrder [(`x, 8), (`i, 2)] [(`o, 8)]
    [ Item.array `a 2 8,
      Item.stmt (.assign `o (.elem `a 8 1)),
      Item.stmt (.setDyn `a 8 (.var `i) (.var `x)) ]

#guard dynOrder.settleOrder.steps.map Stmt.targets = [[.whole `a], [.sig `o]]
#guard (dynOrder.settle (dynOrder.initState.apply [(`x, w8 42), (`i, w2 1)])).toOption.bind
  (State.valueOf? · `o) = some 42

/-- **One statement reading several elements of one array.** The writers come after it in source
order, so the schedule has to move it to the end.

This is the shape that broke, and it broke quietly. The reader index is keyed by *name*, so a
statement reading three elements of `a` was listed under `a` three times; the decrement that
follows a completed driver rescans the reader's uses, so it ran three times too, and the reader's
count reached zero after the **first** driver. It was then scheduled ahead of the other two and
read values nothing had written. No cycle, so `unresolved` stayed empty and nothing in the package
noticed until `meshSwitch` -- whose `anyReq[j]` ors five elements of one array -- lost every packet
that crossed a switch boundary, in the netlist only, where an undriven read is a hard zero rather
than a stale value.

The three elements take *different* values on purpose: with the bug the output still had `a[0]`
in it, so a test whose elements agreed would have passed. -/
private def multiRead : Module :=
  Module.ofItems `multiRead [(`x, 8)] [(`o, 8)]
    [ Item.array `a 3 8,
      Item.stmt (.assign `o
        (.bin .add 8 (.elem `a 8 0) (.bin .add 8 (.elem `a 8 1) (.elem `a 8 2)))),
      Item.stmt (.setElem `a 8 0 (.var `x)),
      Item.stmt (.setElem `a 8 1 (.lit 8 2)),
      Item.stmt (.setElem `a 8 2 (.lit 8 4)) ]

#guard multiRead.settleOrder.unresolved = []
#guard multiRead.settleOrder.steps.map Stmt.targets
  = [[.elem `a 0], [.elem `a 1], [.elem `a 2], [.sig `o]]
#guard (multiRead.settle (multiRead.initState.apply [(`x, w8 9)])).toOption.bind
  (State.valueOf? · `o) = some 15

/-- The negative control for arrays: a cycle *through* two elements is still a cycle, and is
reported as the two elements rather than as the array. -/
private def arrLoop : Module :=
  Module.ofItems `arrLoop [] [(`o, 1)]
    [ Item.array `a 2 1,
      Item.stmt (.setElem `a 1 0 (.elem `a 1 1)),
      Item.stmt (.setElem `a 1 1 (.elem `a 1 0)),
      Item.stmt (.assign `o (.elem `a 1 0)) ]

#guard arrLoop.settleOrder.unresolved = [.elem `a 1, .elem `a 0]

/-! ### The mesh, which is the case the file was written for

`meshSwitch` on its own has always been orderable -- the loop only appears once two of them face
each other. So the switch proves nothing here and the mesh is the test.

**These two numbers are load-bearing.** Removing the output register from `meshSwitch` -- making
`oJ.valid`/`oJ.data` combinational in the inputs again, or putting an `oJ.ready` term back into
`iK.ready` -- sends `mesh4x4`'s `unresolved` from zero to the hundreds. That is the regression this
guards, and it is not visible from any end-to-end test: the old switch delivered flits under
`Module.settle` perfectly well.
-/

#guard (meshSwitch 13).settleOrder.unresolved = []
#guard (mesh4x4 13).settleOrder.unresolved = []

-- Not vacuous: the mesh really does have logic to order, and a good deal of it.
--
-- 1920 and not the 1600 it was while an array port was `n` scalars. Binding a scalar port is a
-- *renaming*, which costs no statement; an array port cannot be renamed through -- `Expr.rename`
-- maps an array by name, and a switch's five inputs come from five scattered slots -- so each of
-- the thirty array-port wires is connected instead: +480 across sixteen switches. The switch then
-- gave back 160 of them, since reading `i[own[j]].data` straight from the port is what let it
-- delete the two copy arrays it used to need (-10 statements apiece).
--
-- The connections cost nothing in the IR: a combinational `setElem` lowers to a scope rebinding,
-- so the mesh is still 320 `seq.firreg`s and 7221 lines, the figures in `CircuitHdlTest/Mesh4x4`,
-- unmoved across the whole change. What they cost is here, in the length of what gets sorted.
#guard (mesh4x4 13).settleOrder.steps.length = 1920
#guard (meshSwitch 13).settleOrder.steps.length = 85

end CircuitHdl
