import CircuitHdl

/-!
Tests for the clock-domain analysis.

These exercise `Clocks.lean` on small modules written to isolate one rule each -- what the analysis
accepts, what it rejects, and where the boundary sits. The analysis applied to a real design is in
`CircuitHdlAsyncFifoTest`, where the FIFO's own domain partition is checked and proved.

A register belongs to the clock that drives it. Two clocks driving one register is a race:
whichever edge lands second wins, and across independent clocks the two have no defined order at
all.
-/

namespace CircuitHdl

open Lean

/-! ### What the analysis rejects -/

module! raced #[] (ca : 1, cb : 1) -> (q : 1) {
  reg q : 1;
  always @(posedge ca) { assign q = 1; }
  always @(posedge cb) { assign q = 0; }
}

#guard !raced.singleClocked
#guard raced.multiplyClocked = [(`q, [`ca, `cb])]

-- A memory written from two domains is the same race, so memories are checked alongside registers.
module! racedMem #[] (ca : 1, cb : 1, d : 8) -> (y : 1) {
  reg m[4] : 8;
  assign y = ca;
  always @(posedge ca) { assign m[(0 : 2)] = d; }
  always @(posedge cb) { assign m[(1 : 2)] = d; }
}

#guard !racedMem.singleClocked
#guard racedMem.multiplyClocked = [(`m, [`ca, `cb])]

/-! ### What it accepts -/

-- Two clocks are fine as long as each register belongs to one of them.
module! twoDomains #[] (ca : 1, cb : 1) -> (qa : 4, qb : 4) {
  reg qa : 4;
  reg qb : 4;
  always @(posedge ca) { assign qa = qa + 1; }
  always @(posedge cb) { assign qb = qb + 1; }
}

#guard twoDomains.singleClocked
#guard twoDomains.clockDomains = [(`qa, [`ca]), (`qb, [`cb])]

-- Two processes on the *same* clock are not a race, so one clock listed twice collapses to one.
module! sameClockTwice #[] (clk : 1) -> (q : 4, r : 4) {
  reg q : 4;
  reg r : 4;
  always @(posedge clk) { assign q = q + 1; }
  always @(posedge clk) { assign r = r + 1; }
}

#guard sameClockTwice.singleClocked
#guard sameClockTwice.clockDomains = [(`q, [`clk]), (`r, [`clk])]

-- A combinational signal has no clock, which is correct rather than a gap: there is no edge that
-- drives it, so there is nothing for two clocks to disagree about.
module! noClock #[] (a : 1, b : 1) -> (y : 1) {
  wire t : 1;
  assign t = a & b;
  assign y = t;
}

#guard noClock.singleClocked
#guard noClock.clockDomains = [(`t, [])]
#guard noClock.multiplyClocked = []

/-! ### Where the boundary sits -/

-- A register assigned on only one branch of an `if` still belongs to that process's clock: which
-- branch runs is a run-time matter, the clock is not.
module! condAssign #[] (clk : 1, c : 1) -> (q : 4) {
  reg q : 4;
  always @(posedge clk) { if c { assign q = q + 1; } else { } }
}
#guard condAssign.clockDomains = [(`q, [`clk])]

-- Nested branches are reached too.
module! nestedAssign #[] (clk : 1, c : 1, d : 1) -> (q : 4) {
  reg q : 4;
  always @(posedge clk) {
    if c { if d { assign q = q + 1; } else { assign q = 0; } } else { }
  }
}

#guard nestedAssign.clockDomains = [(`q, [`clk])]

-- `negedge` is a clock like any other, and mixing edges on one signal is still one domain.
module! bothEdges #[] (clk : 1) -> (q : 4, r : 4) {
  reg q : 4;
  reg r : 4;
  always @(posedge clk) { assign q = q + 1; }
  always @(negedge clk) { assign r = r + 1; }
}

#guard bothEdges.singleClocked
#guard bothEdges.clockDomains = [(`q, [`clk]), (`r, [`clk])]

-- Reading a signal from another domain is not a write, so it does not create a second driver.
-- This is what makes a synchronizer legal: `q2` reads `foreign` but only `clk` drives it.
module! readsForeign #[] (clk : 1, foreign : 4) -> (q : 4) {
  reg q : 4;
  always @(posedge clk) { assign q = foreign; }
}

#guard readsForeign.singleClocked
#guard readsForeign.clockDomains = [(`q, [`clk])]

/-! ### `driversOf` on a single name

`clockDomains` answers for every signal at once; `driversOf` answers for one.
-/

#guard twoDomains.driversOf `qa = [`ca]
#guard twoDomains.driversOf `qb = [`cb]
#guard raced.driversOf `q = [`ca, `cb]
-- A name that is not driven, and one that is not declared, both come back empty.
#guard noClock.driversOf `t = []
#guard twoDomains.driversOf `nosuch = []

end CircuitHdl
