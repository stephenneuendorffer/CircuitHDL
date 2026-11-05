import CircuitHdl.Core
import CircuitHdl.Examples.MeshSwitch

/-!
The 4x4 mesh: sixteen `meshSwitch` instances and the links between them.

**Assembled by a Lean function, not by the surface syntax.** `module!` has no loop -- which is why
`ShiftFifo.lean` fixes its depth at four -- but `Module.ofItems` is an ordinary function taking a
`List Item`, and `wire x : w;` is just `Item.reg`. So the no-loop limitation applies to the
*syntax*, not to module construction, and the 144 link wires and 16 instances are generated from
the coordinates rather than written out. Writing them by hand would be about 160 port bindings
with nothing to catch a transposed index.

### How it is wired

A link `L(x, y, d)` carries flits out of node `(x, y)` in direction `d`, using the same direction
codes as the switch: `0` east, `1` west, `2` north, `3` south.

- switch `(x,y)` output `j` drives `L(x, y, j)` for `j < 4`; output `4` is the ejection port;
- switch `(x,y)` input `k` is fed by the neighbour in direction `k`, through *that* neighbour's
  output in the opposite direction -- so input `0` (the east side) reads `L(x+1, y, 1)`;
- input `4` is the injection port.

### Edges

A node on the boundary has directions with no neighbour. Those are generated, not special-cased:
the missing input is tied to `valid = 0`, and the output that leads nowhere has its `ready` tied
high so the switch is never blocked by a port that does not exist.

Nothing is ever *sent* that way. `xyRoute` only names a direction when the destination is strictly
beyond the current node in it, so an in-bounds destination never routes off the edge -- which is a
property of the policy, proved in `MeshRoutingModel`, and not something the wiring enforces.
-/

namespace CircuitHdl

open Lean

/-- The mesh is 4x4, matching `mesh4x4Model`. -/
private def meshSize : Nat := 4

/-- Where direction `d` leads from `(x, y)`, when it stays inside the mesh. -/
private def neighbour (x y d : Nat) : Option (Nat × Nat) :=
  match d with
  | 0 => if x + 1 < meshSize then some (x + 1, y) else none
  | 1 => if 0 < x then some (x - 1, y) else none
  | 2 => if y + 1 < meshSize then some (x, y + 1) else none
  | 3 => if 0 < y then some (x, y - 1) else none
  | _ => none

/-- The direction facing back the way `d` came. -/
private def opposite : Nat → Nat
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | d => d

private def nodes : List (Nat × Nat) :=
  (List.range meshSize).flatMap fun x => (List.range meshSize).map fun y => (x, y)

private def dirs : List Nat := [0, 1, 2, 3]

/-! ### Names

Flat names rather than the `axis` interface, because the interface only exists inside `module!`
and this module is built directly. -/

private def lnk (x y d : Nat) (field : String) : Name :=
  Name.mkSimple s!"l{x}{y}{d}_{field}"
private def inj (x y : Nat) (field : String) : Name := Name.mkSimple s!"inj{x}{y}_{field}"
private def ej (x y : Nat) (field : String) : Name := Name.mkSimple s!"ej{x}{y}_{field}"
private def coord (x y : Nat) (which : String) : Name := Name.mkSimple s!"{which}{x}{y}"
/-- A sink for an output that leads off the edge. Nothing reads it. -/
private def dead (x y d : Nat) (field : String) : Name :=
  Name.mkSimple s!"dead{x}{y}{d}_{field}"

/-- A switch port name. These are *hierarchical* -- the `module!` syntax builds `i0.valid` as
`i0 ++ valid`, not as a simple name containing a dot -- and binding to a simple name with a dot in
it fails with "not a port of the module it instantiates". -/
private def swPort (port field : String) : Name :=
  Name.mkSimple port ++ Name.mkSimple field

/-! ### The module -/

/-- The 4x4 mesh of wormhole switches. `fw` is the flit width; bits 0 to 4 are the header. -/
def mesh4x4 (fw : Nat) : Module :=
  let inputs : List (Name × Nat) :=
    [(`clk, 1), (`rst, 1)]
    ++ nodes.flatMap (fun (x, y) => [(inj x y "valid", 1), (inj x y "data", fw)])
    ++ nodes.map (fun (x, y) => (ej x y "ready", 1))
  let outputs : List (Name × Nat) :=
    nodes.map (fun (x, y) => (inj x y "ready", 1))
    ++ nodes.flatMap (fun (x, y) => [(ej x y "valid", 1), (ej x y "data", fw)])

  -- Every link's three wires, whether or not it leads anywhere.
  let linkWires : List Item :=
    nodes.flatMap fun (x, y) => dirs.flatMap fun d =>
      [Item.reg (lnk x y d "valid") 1, Item.reg (lnk x y d "ready") 1,
       Item.reg (lnk x y d "data") fw]
  -- Each switch's own coordinates, as constants it can compare against.
  let coordWires : List Item :=
    nodes.flatMap fun (x, y) => [Item.reg (coord x y "mx") 2, Item.reg (coord x y "my") 2]
  let coordDrives : List Item :=
    nodes.flatMap fun (x, y) =>
      [Item.stmt (.assign (coord x y "mx") (.lit 2 x)),
       Item.stmt (.assign (coord x y "my") (.lit 2 y))]
  -- Boundary tie-offs: an absent neighbour offers nothing and accepts everything.
  let edgeWires : List Item :=
    nodes.flatMap fun (x, y) => dirs.flatMap fun d =>
      if (neighbour x y d).isSome then [] else
        -- `ready` is an *output* of the switch, so it needs a sink even though nothing reads it.
        [Item.reg (dead x y d "valid") 1, Item.reg (dead x y d "data") fw,
         Item.reg (dead x y d "ready") 1]
  let edgeDrives : List Item :=
    nodes.flatMap fun (x, y) => dirs.flatMap fun d =>
      if (neighbour x y d).isSome then [] else
        -- The link out of this edge is never taken, so hold its `ready` high rather than letting
        -- an undriven wire read as zero and wedge the switch.
        [Item.stmt (.assign (lnk x y d "ready") (.lit 1 1)),
         Item.stmt (.assign (dead x y d "valid") (.lit 1 0)),
         Item.stmt (.assign (dead x y d "data") (.lit fw 0))]

  -- One switch per node. Input `k` reads the neighbour in direction `k`, through that
  -- neighbour's output in the opposite direction.
  let switches : List Item :=
    nodes.map fun (x, y) =>
      let inBind : List (Name × Name) :=
        dirs.flatMap fun k =>
          match neighbour x y k with
          | some (nx, ny) =>
              let j := opposite k
              [(swPort s!"i{k}" "valid", lnk nx ny j "valid"),
               (swPort s!"i{k}" "ready", lnk nx ny j "ready"),
               (swPort s!"i{k}" "data", lnk nx ny j "data")]
          | none =>
              [(swPort s!"i{k}" "valid", dead x y k "valid"),
               (swPort s!"i{k}" "ready", dead x y k "ready"),
               (swPort s!"i{k}" "data", dead x y k "data")]
      let outBind : List (Name × Name) :=
        dirs.flatMap fun j =>
          [(swPort s!"o{j}" "valid", lnk x y j "valid"),
           (swPort s!"o{j}" "ready", lnk x y j "ready"),
           (swPort s!"o{j}" "data", lnk x y j "data")]
      Item.inst (Name.mkSimple s!"sw{x}{y}") (meshSwitch fw)
        ([(`clk, `clk), (`rst, `rst),
          (`myX, coord x y "mx"), (`myY, coord x y "my"),
          -- Local injection and ejection.
          (`i4.valid, inj x y "valid"), (`i4.ready, inj x y "ready"),
          (`i4.data, inj x y "data"),
          (`o4.valid, ej x y "valid"), (`o4.ready, ej x y "ready"),
          (`o4.data, ej x y "data")] ++ inBind ++ outBind)

  Module.ofItems `mesh4x4 inputs outputs
    (linkWires ++ coordWires ++ edgeWires ++ coordDrives ++ edgeDrives ++ switches)

end CircuitHdl
