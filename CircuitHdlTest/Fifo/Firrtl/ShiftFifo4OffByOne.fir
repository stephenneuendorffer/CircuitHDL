; `ShiftFifo4.fir` with one token changed: `widx` corrects for the wrong handshake, subtracting
; the write that is landing instead of the read that is shifting every slot down. A word accepted
; on a cycle that also hands one out therefore lands one slot too low, and a word accepted into
; an empty FIFO lands at index seven and is dropped.
;
; This is `shiftFifoOffByOne` from `CircuitHdlTest/Fifo/Shift.lean` committed in another
; language. It is here because a check that cannot fail proves nothing: without it,
; `firrtl_refines_queue_burst` might be reporting that the FIRRTL path returns `true` whatever it
; is handed -- that the parse silently produced an empty module, say, or that the bridge read the
; registers out of the harness's own state and never consulted the IR.
;
; Its value is in *which* model rejects it. The occupancy is still right at every tick, because
; `count` is updated correctly and only the data lands in the wrong place, so the counting model
; accepts it and only the contents model refuses. That asymmetry is the same one the Lean design
; exhibits, which is what says the two models keep their separate jobs across the language
; boundary rather than by something particular to `module!`.
;
; **The bug has to leave `widx` a different value from `count`**, and the first version of this
; file did not. Dropping the correction entirely -- `node widx = count`, which is the mutation the
; Lean design carries -- makes the two names alias, and firtool resolves the alias by *renaming
; the register to `widx`*. The compiled module then has no `seq.firreg` named `count` at all, so
; `firrtlAbstractionOf` read nothing, every schedule errored, and both models rejected the design
; for a reason that had nothing to do with the bug. The symptom was
; `firrtl_offByOne_passes_counting` coming out `false`; `firrtlRegs` pins the register names now,
; so a mutation absorbed into a renaming is reported as a changed pin instead.

FIRRTL version 4.0.0
circuit ShiftFifo4OffByOne :
  public module ShiftFifo4OffByOne :
    input clk : UInt<1>
    input rst : UInt<1>
    input s_valid : UInt<1>
    input s_data : UInt<8>
    input m_ready : UInt<1>
    output m_valid : UInt<1>
    output m_data : UInt<8>
    output s_ready : UInt<1>

    node clock = asClock(clk)

    reg count : UInt<3>, clock
    reg r0 : UInt<8>, clock
    reg r1 : UInt<8>, clock
    reg r2 : UInt<8>, clock
    reg r3 : UInt<8>, clock

    node notRst = not(rst)
    node sRdy = and(notRst, not(eq(count, UInt<3>(4))))
    node mVld = and(notRst, not(eq(count, UInt<3>(0))))
    connect s_ready, sRdy
    connect m_valid, mVld
    connect m_data, r0

    node wfire = and(s_valid, sRdy)
    node rfire = and(mVld, m_ready)
    node wf3 = pad(wfire, 3)
    node rf3 = pad(rfire, 3)

    ; The one changed token. `ShiftFifo4.fir` subtracts `rf3` here.
    node widx = tail(sub(count, wf3), 1)

    node cmid = tail(add(count, wf3), 1)
    node cnext = tail(sub(cmid, rf3), 1)

    connect count, mux(rst, UInt<3>(0), cnext)
    connect r0, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(0))), s_data, mux(rfire, r1, r0)))
    connect r1, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(1))), s_data, mux(rfire, r2, r1)))
    connect r2, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(2))), s_data, mux(rfire, r3, r2)))
    connect r3, mux(rst, UInt<8>(0), mux(and(wfire, eq(widx, UInt<3>(3))), s_data, r3))
