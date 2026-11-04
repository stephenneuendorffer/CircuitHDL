/-!
What a routing policy on a rectangular mesh is, and what makes one deadlock-free.

No hardware here, and nothing specific to a 4x4: this is the theory a switch implementation is
later checked against, in the same sense that `AbstractFifoModel` is the theory a FIFO is checked
against. It is also the only place in the package where the headline property is **kernel**-proved
rather than `native_decide`d over a bounded set of schedules -- which is the point, because
deadlock freedom is not a property any finite simulation could establish.

### The argument

Deadlock in a wormhole network is a cycle of blocked packets: each holds a channel and waits for
one held by the next. Dally and Seitz's observation is that this can only happen if the *channel
dependency graph* has a cycle -- the graph whose edges are "some packet can hold `c₁` and then
ask for `c₂`". So a routing function with an acyclic dependency graph cannot deadlock, whatever
the traffic.

The acyclicity is proved here by **ranking the channels** rather than by enumerating the graph.
Assign each channel a number such that every dependency edge strictly increases it, and a cycle
would need `rank c < rank c`. Three things fall out of doing it that way:

- it holds for a mesh of any size, not just the 4x4 the hardware is built for;
- it is cheap enough to be a kernel proof, where deciding acyclicity of the ~1500 edges a 4x4
  generates would be a `native_decide` over a list the kernel cannot reduce;
- the *reason* XY routing works becomes visible in the rank function, instead of being a fact
  about a graph nobody can read.

### What the rank encodes

A packet under dimension-order routing travels in X and then in Y, never the other way. So:

- within the X phase it moves monotonically toward the destination's column, so its X channels
  have strictly increasing rank;
- the same within the Y phase;
- and every Y channel outranks every X channel, so the one turn a packet makes also increases.

The Y-to-X turn, which would close a cycle, simply has no dependency edge: a packet moving in Y
is already in the destination's column, so it can never ask for an X channel again. That is the
whole of the theorem.

### Multi-cycle traversal is irrelevant here

How many cycles a packet takes to cross a switch changes *when* a channel is held, not *which*
channels it can ask for. The dependency graph, and so everything below, is unaffected -- which is
why the implementation is free to pipeline the switch however it likes.
-/

namespace CircuitHdl

/-! ### The mesh -/

/-- A rectangular mesh: the thing a routing policy is a policy *for*.

Everything in this file is stated against an arbitrary one. `mesh4x4Model` is the instance the
hardware is built around, and nothing below knows that. -/
structure MeshRoutingModel where
  width : Nat
  height : Nat
  deriving Repr, DecidableEq

/-- A position in the mesh. -/
structure Node where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The four directions a packet can leave a node by.

There is no `local` here. Injection and ejection are not channels a packet competes for in the
sense that matters -- a packet being ejected is leaving the network, so it releases rather than
acquires, and can never be part of a wait-for cycle. -/
inductive Dir where
  | east | west | north | south
  deriving Repr, DecidableEq, Inhabited

/-- A channel is the link *out of* a node in a direction. Naming them by their source rather than
as unordered pairs is what lets `rank` be a function of one coordinate. -/
abbrev Channel := Node × Dir

/-- Where a direction leads. `west` and `south` use truncating subtraction, which is only ever
reached with a positive coordinate -- `xyRoute` returns them only when the destination is strictly
lower. -/
def Node.step (n : Node) : Dir → Node
  | .east => ⟨n.x + 1, n.y⟩
  | .west => ⟨n.x - 1, n.y⟩
  | .north => ⟨n.x, n.y + 1⟩
  | .south => ⟨n.x, n.y - 1⟩

/-- Inside the mesh. Carried through the dependency relation because `rank` separates X channels
from Y channels by `width`, and that separation needs the X coordinate to be bounded. -/
def MeshRoutingModel.InBounds (m : MeshRoutingModel) (n : Node) : Prop :=
  n.x < m.width ∧ n.y < m.height

/-! ### Dimension-order routing -/

/-- Dimension-order (XY) routing: close the X gap first, then the Y gap.

`none` at the destination is what makes this total without a separate "arrived" flag, and is the
base case of the progress argument. -/
def xyRoute (cur dst : Node) : Option Dir :=
  if cur.x < dst.x then some .east
  else if dst.x < cur.x then some .west
  else if cur.y < dst.y then some .north
  else if dst.y < cur.y then some .south
  else none

/-- A routing policy: where to send a packet at `cur` bound for `dst`. Stated as a parameter
rather than fixed to `xyRoute`, so that a policy which *does* deadlock can be written down and the
theorem seen to fail for it -- see `mixedRoute`. -/
abbrev Policy := Node → Node → Option Dir

/-! #### What each answer tells you

The dependency proof never unfolds `xyRoute` directly. These four lemmas are the whole interface
to it, and each says exactly what a routing decision reveals about the packet's position. The two
Y cases carrying `cur.x = dst.x` is the fact the acyclicity rests on: a packet moving in Y has
finished with X forever.
-/

theorem xyRoute_east {cur dst : Node} (h : xyRoute cur dst = some .east) : cur.x < dst.x := by
  by_cases h1 : cur.x < dst.x
  · exact h1
  · exfalso
    by_cases h2 : dst.x < cur.x
    · simp [xyRoute, h1, h2] at h
    · by_cases h3 : cur.y < dst.y
      · simp [xyRoute, h1, h2, h3] at h
      · by_cases h4 : dst.y < cur.y <;> simp [xyRoute, h1, h2, h3, h4] at h

theorem xyRoute_west {cur dst : Node} (h : xyRoute cur dst = some .west) : dst.x < cur.x := by
  by_cases h1 : cur.x < dst.x
  · simp [xyRoute, h1] at h
  · by_cases h2 : dst.x < cur.x
    · exact h2
    · exfalso
      by_cases h3 : cur.y < dst.y
      · simp [xyRoute, h1, h2, h3] at h
      · by_cases h4 : dst.y < cur.y <;> simp [xyRoute, h1, h2, h3, h4] at h

theorem xyRoute_north {cur dst : Node} (h : xyRoute cur dst = some .north) :
    cur.x = dst.x ∧ cur.y < dst.y := by
  by_cases h1 : cur.x < dst.x
  · simp [xyRoute, h1] at h
  · by_cases h2 : dst.x < cur.x
    · simp [xyRoute, h1, h2] at h
    · by_cases h3 : cur.y < dst.y
      · exact ⟨by omega, h3⟩
      · by_cases h4 : dst.y < cur.y <;> simp [xyRoute, h1, h2, h3, h4] at h

theorem xyRoute_south {cur dst : Node} (h : xyRoute cur dst = some .south) :
    cur.x = dst.x ∧ dst.y < cur.y := by
  by_cases h1 : cur.x < dst.x
  · simp [xyRoute, h1] at h
  · by_cases h2 : dst.x < cur.x
    · simp [xyRoute, h1, h2] at h
    · by_cases h3 : cur.y < dst.y
      · simp [xyRoute, h1, h2, h3] at h
      · by_cases h4 : dst.y < cur.y
        · exact ⟨by omega, h4⟩
        · simp [xyRoute, h1, h2, h3, h4] at h

/-! ### The channel dependency graph -/

/-- `c₁` depends on `c₂` when some packet can traverse `c₁` and then immediately ask for `c₂`.

Quantifying over the destination is what makes this exact rather than conservative: a packet is
only on `c₁` because the policy sent it there, and the *same* destination then decides `c₂`. That
is how "a packet moving in Y is already in the right column" gets into the relation without being
stated -- it is a consequence of `route n₁ dst = some .north`. -/
def Depends (m : MeshRoutingModel) (route : Policy) (c₁ c₂ : Channel) : Prop :=
  ∃ dst : Node,
    m.InBounds c₁.1 ∧ m.InBounds dst ∧
    route c₁.1 dst = some c₁.2 ∧
    c₂.1 = c₁.1.step c₁.2 ∧
    route c₂.1 dst = some c₂.2

/-- Transitive reachability in the dependency graph. A cycle is exactly `Reaches c c`, and that is
what a deadlock needs. -/
inductive Reaches (m : MeshRoutingModel) (route : Policy) : Channel → Channel → Prop
  | single {a b} : Depends m route a b → Reaches m route a b
  | step {a b c} : Depends m route a b → Reaches m route b c → Reaches m route a c

/-! ### The rank

X channels below `width`, Y channels at or above it, and each dimension's two directions ranked
so that a packet travelling in either one climbs.

`east` and `west` share a range, and so do `north` and `south`. That is sound because no packet
ever reverses: a packet going east has `cur.x < dst.x`, so after one step it still does not want
to go west. There is no edge between them to order.
-/

def MeshRoutingModel.rank (m : MeshRoutingModel) : Channel → Nat
  | (n, .east) => n.x
  | (n, .west) => m.width - 1 - n.x
  | (n, .north) => m.width + n.y
  | (n, .south) => m.width + (m.height - 1 - n.y)

/-- **Every dependency edge strictly increases the rank.**

Sixteen cases, of which six are impossible: the four Y-to-X turns, and the two reversals. `omega`
closes the rest from the four `xyRoute_*` lemmas and the in-bounds hypothesis. -/
theorem rank_lt_of_depends (m : MeshRoutingModel) {c₁ c₂ : Channel}
    (h : Depends m xyRoute c₁ c₂) : m.rank c₁ < m.rank c₂ := by
  obtain ⟨dst, ⟨hx1, hy1⟩, ⟨hdx, hdy⟩, h1, hstep, h2⟩ := h
  obtain ⟨n₁, d₁⟩ := c₁
  obtain ⟨n₂, d₂⟩ := c₂
  simp only at h1 hstep h2 hx1 hy1
  subst hstep
  cases d₁ <;> cases d₂ <;>
    simp only [Node.step, MeshRoutingModel.rank] at *
  all_goals
    first
    | (have e1 := xyRoute_east h1; try have e2 := xyRoute_east h2
       try have w2 := xyRoute_west h2
       try obtain ⟨n2x, n2y⟩ := xyRoute_north h2
       try obtain ⟨s2x, s2y⟩ := xyRoute_south h2
       simp only [] at *; omega)
    | (have w1 := xyRoute_west h1; try have e2 := xyRoute_east h2
       try have w2 := xyRoute_west h2
       try obtain ⟨n2x, n2y⟩ := xyRoute_north h2
       try obtain ⟨s2x, s2y⟩ := xyRoute_south h2
       simp only [] at *; omega)
    | (obtain ⟨n1x, n1y⟩ := xyRoute_north h1
       try have e2 := xyRoute_east h2
       try have w2 := xyRoute_west h2
       try obtain ⟨n2x, n2y⟩ := xyRoute_north h2
       try obtain ⟨s2x, s2y⟩ := xyRoute_south h2
       simp only [] at *; omega)
    | (obtain ⟨s1x, s1y⟩ := xyRoute_south h1
       try have e2 := xyRoute_east h2
       try have w2 := xyRoute_west h2
       try obtain ⟨n2x, n2y⟩ := xyRoute_north h2
       try obtain ⟨s2x, s2y⟩ := xyRoute_south h2
       simp only [] at *; omega)

/-- Rank increases along any chain, by induction on it. -/
theorem rank_lt_of_reaches (m : MeshRoutingModel) {a b : Channel}
    (h : Reaches m xyRoute a b) : m.rank a < m.rank b := by
  induction h with
  | single hd => exact rank_lt_of_depends m hd
  | step hd _ ih => exact Nat.lt_trans (rank_lt_of_depends m hd) ih

/-- **The channel dependency graph of XY routing is acyclic**, on a mesh of any size.

This is the Dally-Seitz condition, and it is kernel-checked: `#print axioms` on it shows no
`_native.*`. -/
theorem xy_acyclic (m : MeshRoutingModel) (c : Channel) : ¬ Reaches m xyRoute c c := by
  intro h
  exact Nat.lt_irrefl _ (rank_lt_of_reaches m h)

/-! ### From an acyclic graph to no deadlock -/

/-- A blocked packet: it has acquired `held` and cannot proceed until it acquires `wants`.

Wormhole switching means a packet may hold a *chain* of channels at once, stretched across several
switches. That costs nothing here: each held channel contributes its own entry, and each entry's
request is still a dependency edge. -/
structure Blocked where
  held : Channel
  wants : Channel
  deriving Repr, DecidableEq

/-- `a` waits on `b`, directly or through a chain of blocked packets: `a` wants the channel `b`
holds, and `b` is itself blocked.

The `Depends` premise on each link is the legality condition -- every packet's request follows the
routing policy. Carrying it in the relation rather than as a separate hypothesis is what lets the
induction go through without a list. -/
inductive WaitsOn (m : MeshRoutingModel) (route : Policy) : Blocked → Blocked → Prop
  | direct {a b} : Depends m route a.held a.wants → a.wants = b.held → WaitsOn m route a b
  | trans {a b c} : Depends m route a.held a.wants → a.wants = b.held →
      WaitsOn m route b c → WaitsOn m route a c

/-- A wait-for chain is a dependency chain on the channels it runs through. -/
theorem reaches_of_waitsOn (m : MeshRoutingModel) {route : Policy} {a b : Blocked}
    (h : WaitsOn m route a b) : Reaches m route a.held b.held := by
  induction h with
  | direct hd heq => exact .single (heq ▸ hd)
  | trans hd heq _ ih => exact .step (heq ▸ hd) ih

/-- **A packet routed by XY can never wait on itself**, so no set of blocked packets can close a
wait-for cycle, so the network cannot deadlock.

This holds for any mesh size, any traffic, any number of packets, and any per-switch latency --
none of which appear in the statement, because none of them matter. -/
theorem xy_no_deadlock (m : MeshRoutingModel) (p : Blocked) : ¬ WaitsOn m xyRoute p p := by
  intro h
  exact xy_acyclic m p.held (reaches_of_waitsOn m h)

/-! ### The mesh the hardware is built for -/

/-- The 4x4 instance. Nothing above depends on it. -/
def mesh4x4Model : MeshRoutingModel := ⟨4, 4⟩

/-! ### The theorem is about XY, and not about routing in general

`xy_no_deadlock` would be worth nothing if it held of any policy whatsoever, so here is one it
does not hold of.

`mixedRoute` picks the dimension order from the parity of the current node: some nodes send X
first, some send Y first. Each decision is individually sensible and every packet still makes
progress toward its destination -- what it loses is the single global order on the dimensions,
and with it the rank. Four channels around one unit square then depend on each other in a ring.

This is the classic reason dimension-order routing is *dimension-order* rather than merely
shortest-path, and the cycle below is what `rank_lt_of_depends` is ruling out.
-/

/-- Shortest-path routing that chooses its dimension order per node. Deadlocks. -/
def mixedRoute (cur dst : Node) : Option Dir :=
  if (cur.x + cur.y) % 2 == 0 then xyRoute cur dst
  else
    -- The other order: close Y first, then X.
    if cur.y < dst.y then some .north
    else if dst.y < cur.y then some .south
    else if cur.x < dst.x then some .east
    else if dst.x < cur.x then some .west
    else none

/-- The ring, going anticlockwise around the square with corners `(1,1)` and `(2,2)`.

Each step is a real packet with a real destination: at `(1,1)` the parity is even so X goes first
and a packet for `(2,2)` leaves east; at `(2,1)` the parity is odd so Y goes first and a packet
for `(1,2)` leaves north; and so on round. Four packets in those four positions wait on each
other forever. -/
theorem mixed_has_a_cycle :
    Reaches mesh4x4Model mixedRoute (⟨1,1⟩, .east) (⟨1,1⟩, .east) := by
  have e1 : Depends mesh4x4Model mixedRoute (⟨1,1⟩, .east) (⟨2,1⟩, .north) := by
    refine ⟨⟨2,2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  have e2 : Depends mesh4x4Model mixedRoute (⟨2,1⟩, .north) (⟨2,2⟩, .west) := by
    refine ⟨⟨1,2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  have e3 : Depends mesh4x4Model mixedRoute (⟨2,2⟩, .west) (⟨1,2⟩, .south) := by
    refine ⟨⟨1,1⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  have e4 : Depends mesh4x4Model mixedRoute (⟨1,2⟩, .south) (⟨1,1⟩, .east) := by
    refine ⟨⟨2,1⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide
  exact .step e1 (.step e2 (.step e3 (.single e4)))

/-- So the conclusion of `xy_acyclic` is **false** for `mixedRoute`: there is a channel that
reaches itself, which is exactly a set of packets able to wait on each other forever. -/
theorem mixed_not_acyclic :
    ¬ (∀ c : Channel, ¬ Reaches mesh4x4Model mixedRoute c c) :=
  fun h => h _ mixed_has_a_cycle

end CircuitHdl
