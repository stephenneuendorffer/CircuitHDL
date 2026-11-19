; A shift-register FIFO of depth four and width eight, written in FIRRTL.
;
; This is `CircuitHdl.shiftFifo 4 8` re-implemented in a language this package does not define,
; compiled by a compiler this package does not own. `CircuitHdlTest/Fifo/Firrtl.lean` runs it
; against `AbstractFifoModel` and `AbstractQueueModel` -- the same models, schedules and harness
; the Lean design is checked by. What differs is everything underneath: the source language, the
; frontend, the optimiser, and the shape of the `hw` operations that come out.
;
; FIRRTL rather than Verilog because the CIRCT build on this host has no Verilog frontend:
; `ImportVerilog.h` ships but `circt-verilog` does not, and slang is absent, so Verilog is an
; export format here and cannot be read back. FIRRTL is the one real HDL `firtool` accepts.
;
; The structure follows the Verilog in `CircuitHdl/Examples/Fifo/Shift.lean`'s docstring rather
; than the `module!` source: four separately named registers, not an array. That is what FIRRTL
; makes natural, and it is the point -- a third implementation that shared the Lean design's
; storage layout would be a transcription rather than an independent one. The consequence is
; visible in `Firrtl.lean`, which needs its own abstraction function to read `r0 .. r3` where
; `shiftQueueAbstractionOf` reads one array cell.
;
; Port order is load-bearing. `Veir.Netlist` addresses a module's boundary by block-argument
; position, so these eight ports must be declared in the order `Firrtl.lean` names them.
; `firrtlPorts` pins the order as the compiler reports it, so a reordering here is caught by a
; changed pin rather than by a refinement that mysteriously goes red.

FIRRTL version 4.0.0
circuit ShiftFifo4 :
  public module ShiftFifo4 :
    input clk : UInt<1>
    input rst : UInt<1>
    input s_valid : UInt<1>
    input s_data : UInt<8>
    input m_ready : UInt<1>
    output m_valid : UInt<1>
    output m_data : UInt<8>
    output s_ready : UInt<1>

    ; The clock arrives as a bit and is cast, rather than being declared `Clock`. That is what
    ; makes `firtool` emit `seq.to_clock` of a block argument, which is the only clock form
    ; `Veir.Netlist` accepts.
    node clock = asClock(clk)

    ; `count` is three bits because a full FIFO holds four: it counts 0 to 4, not 0 to 3.
    reg count : UInt<3>, clock
    reg r0 : UInt<8>, clock
    reg r1 : UInt<8>, clock
    reg r2 : UInt<8>, clock
    reg r3 : UInt<8>, clock

    ; Both flags are exact and correct from the first cycle, `count` being local to this clock.
    ; Gating them on `rst` is what makes "no transfer completes during reset" structural.
    node notRst = not(rst)
    node sRdy = and(notRst, not(eq(count, UInt<3>(4))))
    node mVld = and(notRst, not(eq(count, UInt<3>(0))))
    connect s_ready, sRdy
    connect m_valid, mVld
    connect m_data, r0

    node wfire = and(s_valid, sRdy)
    node rfire = and(mVld, m_ready)

    ; FIRRTL widens on every arithmetic operation -- `add` of two `UInt<3>` is a `UInt<4>` -- so
    ; each result is taken back to three bits with `tail`, which drops the leading bit and is
    ; therefore exactly the wrapping the Lean design's `+` and `-` already do.
    node wf3 = pad(wfire, 3)
    node rf3 = pad(rfire, 3)
    ; Where a new word lands: the first free slot, counted after whatever shift this cycle does.
    ; Dropping the `rf3` term here is the off-by-one that `ShiftFifo4OffByOne.fir` exhibits.
    node widx = tail(sub(count, rf3), 1)
    node cmid = tail(add(count, wf3), 1)
    node cnext = tail(sub(cmid, rf3), 1)

    ; Each register resets itself with a mux rather than sitting inside a `when rst`. `firtool`
    ; recognises the shape and emits a `seq.firreg` with a *synchronous reset operand*, which is
    ; a register form `CircuitHdl.Circt` never produces -- it reconciles reset into plain muxes
    ; and emits no reset operand at all. So these registers exercise a path through
    ; `Veir.Netlist` that no theorem in this package reached before.
    connect count, mux(rst, UInt<3>(0), cnext)
    connect r0, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(0))), s_data, mux(rfire, r1, r0)))
    connect r1, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(1))), s_data, mux(rfire, r2, r1)))
    connect r2, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(2))), s_data, mux(rfire, r3, r2)))
    ; The top slot has nothing above it to shift down, so a read leaves it alone.
    connect r3, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(3))), s_data, r3))
