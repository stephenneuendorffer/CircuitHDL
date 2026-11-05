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

private def settledAt (m : Module) (ins : State) (probe : Name) : Option Nat :=
  match m.settle (m.initState.apply ins) with
  | .ok σ => σ.valueOf? probe
  | .error _ => none

-- x = 5 gives a = 6 and b = 7, in one pass, despite `b` being written first.
#guard settledAt reversed [(`x, w4 5)] `a = some 6
#guard settledAt reversed [(`x, w4 5)] `b = some 7

-- And the statements really were reordered, rather than the right answer arriving by luck.
#guard reversed.settleOrder.steps.map Stmt.targets = [[`a], [`b]]
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

#guard forward.settleOrder.steps.map Stmt.targets = [[`a], [`b]]
#guard settledAt forward [(`x, w4 5)] `b = some 7

-- The real designs are all in this case, which is why reordering them changes nothing.
#guard (asyncFifo 4 8 (by decide)).settleOrder.unresolved = []
#guard (shiftFifo4 8).settleOrder.unresolved = []
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
#guard loopy.settleOrder.unresolved.contains `p
#guard loopy.settleOrder.unresolved.contains `q
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
#guard loopyPlus.settleOrder.steps.map Stmt.targets = [[`s], [`p], [`q]]

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
#guard (mesh4x4 13).settleOrder.steps.length = 1440

end CircuitHdl
