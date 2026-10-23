import CircuitHdl.Core
import CircuitHdl.Syntax

/-!
An asynchronous FIFO: the canonical clock-domain-crossing design.

Depth 4, 8-bit data. Pointers are 3 bits -- two address bits plus one extra, which is what lets full
and empty be told apart when the pointers are otherwise equal.

The design follows Cliff Cummings' standard formulation. The part that matters is why **gray** code:
a binary pointer sampled by the other clock domain can be caught mid-transition with several bits
in flight, giving a value that was never actually held. A gray pointer changes exactly one bit per
increment, so the worst a sampler can see is the value just before or just after -- both safe.

Each pointer crosses through a two-flop synchronizer in the destination domain. The flags compare
the local pointer against the synchronized remote one:

- `rempty` when the read pointer has caught up with the write pointer
- `wfull` when the write pointer has lapped the read pointer, which the extra bit detects: the
  gray codes match in the low bits but differ in the top two

Both flags are **registered**, which is also what keeps the combinational chain acyclic:
`bin -> next -> gray -> flag` reads the flag from a register rather than from itself, so a single
ordered settle pass is enough.

There is no reset port. Every register starts at zero, which is the correct empty state, but
`rempty` and `wfull` are registers too and so only become correct one tick into their own domain.
A testbench that checks the flags before ticking will see them low.
-/

namespace CircuitHdl

open Lean

/-! ### The AXI-Stream port

One interface, declared once, rather than three loose wires repeated per port. `fwd` runs with the
port's direction and `rev` against it, which is the only thing that distinguishes `ready` from
`valid` -- and the thing a flat port list cannot say. -/

macro_rules
  | `(circuit_iface| axis $dw:term) =>
      `(circuit_fields| fields! { fwd valid : 1, rev ready : 1, fwd data : $dw })

/-- Binary to gray at any width: `g = b ^ (b >> 1)`.

Instantiated twice by the FIFO, once per clock domain. -/
module! grayOfW #[(w : Nat)] (b : w) -> (g : w) {
  assign g = b ^ (b >> 1);
}

/-- A two-flop synchronizer at any width, the other half of a safe crossing. -/
module! sync2W #[(w : Nat)] (clk : 1, din : w) -> (dout : w) {
  reg q1 : w;
  reg q2 : w;
  always @(posedge clk) {
    assign q1 = din;
    assign q2 = q1;
  }
  assign dout = q2;
}

/-! ### The depth contract

The memory holds `depth` words and every internal width derives from `Nat.log2 depth`, so the two
only agree when `depth` is a power of two. That is a real precondition, not a convention, and it is
enforced at the call site rather than assumed: `asyncFifo 5 8` does not elaborate.

The floor of 4 is the other half of the contract. The full test compares the top *two* pointer bits,
so a design with fewer than two address bits has nothing to compare.
-/

/-- A usable FIFO depth: a power of two, and at least 4. -/
def validDepth (d : Nat) : Bool := 4 ≤ d && d &&& (d - 1) == 0

example : validDepth 4 = true := rfl
example : validDepth 32 = true := rfl
example : validDepth 5 = false := rfl
example : validDepth 2 = false := rfl

/-- Asynchronous FIFO with AXI-style valid/ready handshakes, holding `depth` words of `dw` bits.

`depth` must be a power of two and at least 4; the proof is filled in by `decide` at the call site,
so a bad size is a compile error rather than a silently mis-sized FIFO. Every internal width is
derived from `Nat.log2 depth`: the address is that many bits, and a pointer one more -- the extra
bit is what distinguishes full from empty when the address bits agree.

The write side is an AXI slave port -- `s.valid`/`s.ready`/`s.data` on `wclk` -- and the read side
an AXI master port -- `m.valid`/`m.ready`/`m.data` on `rclk`. A transfer happens on a clock edge
where both halves of a handshake are high.

The handshake rules this satisfies:

- `s.ready` is `~full` and `m.valid` is `~empty`, and both `full` and `empty` are **registers**. So
  neither ready signal depends combinationally on the valid facing it, which is what keeps two
  such FIFOs from forming a loop when connected back to back.
- Once `m.valid` is high it stays high until the transfer completes, because only a completed
  handshake advances the read pointer.
- `s.valid` may be asserted without waiting for `s.ready`, and the write is simply held off until
  the handshake completes.

Gray code is the point of the crossing. A binary pointer sampled by the other clock domain can be
caught mid-transition with several bits in flight, yielding a value it never actually held. A gray
pointer changes exactly one bit per increment, so the worst a sampler sees is the value just before
or just after -- both safe.

`full` is conservative: because the read pointer reaches the write domain two `wclk` ticks late,
`s.ready` can drop while the FIFO has in fact been drained. That is the safe direction -- the
opposite error would overwrite data the reader has not taken.

There is no reset port. Every register starts at zero, which is the correct empty state, but
`rempty` and `wfull` are registers too and so only become correct one tick into their own domain. -/
module! asyncFifo #[(depth dw : Nat) (_h : validDepth depth = true := by decide)]
    (wclk : 1, rclk : 1, slave s : axis dw) -> (master m : axis dw) {
    let n := Nat.log2 depth;
    reg mem[depth] : dw;

    -- Write domain: binary and gray pointers, plus the read pointer synchronized in.
    reg wbin : n+1;
    reg wptr : n+1;
    reg wq1 : n+1;
    reg wq2 : n+1;
    reg wfull : 1;

    -- Read domain, mirrored.
    reg rbin : n+1;
    reg rptr : n+1;
    reg rq1 : n+1;
    reg rq2 : n+1;
    reg rempty : 1;

    wire wfire : 1;
    wire rfire : 1;
    wire wbnext : n+1;
    wire wgnext : n+1;
    wire wfullnext : 1;
    wire rbnext : n+1;
    wire rgnext : n+1;
    wire remptynext : 1;
    wire waddr : n;
    wire raddr : n;

    -- Combinational, in dependency order so one settle pass suffices. Both handshake outputs come
    -- straight off a register, so neither depends on the valid facing it.
    assign s.ready = ~wfull;
    assign m.valid = ~rempty;
    assign wfire = s.valid & s.ready;
    assign rfire = m.valid & m.ready;
    assign wbnext = wbin + {(0 : n), wfire};
    (grayOfW (n+1)) wg (.b(wbnext), .g(wgnext));
    assign wfullnext = wgnext == {~wq2[n:n-1], wq2[n-2:0]};
    assign rbnext = rbin + {(0 : n), rfire};
    (grayOfW (n+1)) rg (.b(rbnext), .g(rgnext));
    assign remptynext = rgnext == rq2;
    assign waddr = wbin[n-1:0];
    assign raddr = rbin[n-1:0];
    assign m.data = mem[raddr];

    always @(posedge wclk) {
      assign wbin = wbnext;
      assign wptr = wgnext;
      assign wq1 = rptr;
      assign wq2 = wq1;
      assign wfull = wfullnext;
      if wfire { assign mem[waddr] = s.data; } else { }
    }

    always @(posedge rclk) {
      assign rbin = rbnext;
      assign rptr = rgnext;
      assign rq1 = wptr;
      assign rq2 = rq1;
      assign rempty = remptynext;
    }
  }

end CircuitHdl
