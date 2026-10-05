import Ruby.Layout
import Ruby.Combinators

/-!
# Netlists

The netlist interpretation of a circuit: wires carry `Net`s (constants,
internal nodes, or bits of top-level ports), wiring renames them, and every
primitive becomes a placed instance. The position of each instance is computed
by the same `Circuit.size` arithmetic as the layout semantics `Circuit.sites`,
so the emitted placement is the one the layout theorems are about
(`Circuit.gen_sites` in `Ruby.NetlistLayout`). Instances record the function a
LUT computes and the nodes they drive, so the netlist has an execution
semantics of its own (`Ruby.NetlistSemantics`).
-/

namespace Ruby

open Shape

/-- A signal of the generated netlist. -/
inductive Net where
  | const (b : Bool)
  | node (id : Nat)
  | port (name : String) (path : List Nat)
  deriving Repr, Inhabited, BEq

/-- A primitive instance and its connections. -/
inductive InstKind where
  /-- A `k`-input LUT computing `f` from the inputs `I0 …`, driving node `out`. -/
  | lut (k : Nat) (f : (Fin k → Bool) → Bool) (ins : Fin k → Net) (out : Nat)
  /-- A CARRY4 with inputs `CI`, `CYINIT`, `DI[3:0]`, `S[3:0]`, driving nodes
  `out … out + 3` (`O`) and `out + 4 … out + 7` (`CO`). -/
  | carry4 (ci cyinit : Net) (di s : Fin 4 → Net) (out : Nat)
  /-- An FDCE with data `D`, driving node `q` (clock, enable and clear are global). -/
  | fdce (d : Net) (q : Nat)
  deriving Inhabited

/-- A primitive instance placed at slice column `x` and LUT row `y`. -/
structure Inst where
  id : Nat
  x : Nat
  y : Nat
  kind : InstKind
  deriving Inhabited

structure NetlistState where
  nextNode : Nat := 0
  insts : Array Inst := #[]

abbrev NetM := StateM NetlistState

/-- Allocate `n` fresh internal nodes, returning the first. -/
def freshBlock (n : Nat) : NetM Nat :=
  modifyGet fun s => (s.nextNode, { s with nextNode := s.nextNode + n })

def emitInst (x y : Nat) (k : InstKind) : NetM Unit :=
  modify fun s => { s with insts := s.insts.push ⟨s.insts.size, x, y, k⟩ }

/-- The `INIT` vector of a LUT computing `f`: bit `i` is `f` on the inputs given by
the binary digits of `i`, with `I0` the least significant. -/
def lutInit (k : Nat) (f : (Fin k → Bool) → Bool) : Nat :=
  (List.range (2 ^ k)).foldl (fun acc idx => if f fun i => idx.testBit i.val then acc + 2 ^ idx else acc) 0

/-- A bundle with every wire set to `v`. -/
def Shape.fill {β : Type} (v : β) : (s : Shape) → s.Val β
  | .bit => v
  | .pair a b => (Shape.fill v a, Shape.fill v b)
  | .vec _ a => fun _ => Shape.fill v a

def Prim.gen {a b : Shape} : Prim a b → Nat → Nat → a.Val Net → NetM (b.Val Net)
  | .lut k f, x, y, v => do
      let o ← freshBlock 1
      emitInst x y (.lut k f v o)
      pure (.node o)
  | .carry4, x, y, v => do
      let o ← freshBlock 8
      emitInst x y (.carry4 v.1.1 v.1.2 v.2.1 v.2.2 o)
      pure (fun i => .node (o + i.val), fun i => .node (o + 4 + i.val))
  | .fdce, x, y, v => do
      let q ← freshBlock 1
      emitInst x y (.fdce v q)
      pure (.node q)

/-- Generate the netlist of `c` placed with its lower left corner at `(x, y)`. -/
def Circuit.gen : {a b : Shape} → Circuit a b → Nat → Nat → a.Val Net → NetM (b.Val Net)
  | _, _, .prim p, x, y, v => p.gen x y v
  | _, _, .wire w, _, _, v => pure (w.run Net.const v)
  | _, _, .seq .beside r s, x, y, v => do
      let u ← r.gen x y v
      s.gen (x + r.size.1) y u
  | _, _, .seq .below r s, x, y, v => do
      let u ← r.gen x y v
      s.gen x (y + r.size.2) u
  | _, _, .seq .overlay r s, x, y, v => do
      let u ← r.gen x y v
      s.gen x y u
  | _, _, .par r s, x, y, v => do
      let u ← r.gen x y v.1
      let w ← s.gen x (y + r.size.2) v.2
      pure (u, w)
  | _, _, .map n r, x, y, v => do
      let outs ← (List.finRange n).mapM fun i => r.gen x (y + i.val * r.size.2) (v i)
      pure fun i => outs.getD i.val (Shape.fill (Net.const false) _)

/-- The input bundle of a top-level port: bit `path` of port `name`. -/
def Shape.portVal (name : String) : (s : Shape) → List Nat → s.Val Net
  | .bit, path => .port name path.reverse
  | .pair a b, path => (Shape.portVal name a (0 :: path), Shape.portVal name b (1 :: path))
  | .vec _ a, path => fun i => Shape.portVal name a (i.val :: path)

/-- The wires of a bundle with their index paths. -/
def Shape.leaves {β : Type} : (s : Shape) → s.Val β → List (List Nat × β)
  | .bit, v => [([], v)]
  | .pair a b, v =>
      (Shape.leaves a v.1).map (fun p => (0 :: p.1, p.2)) ++
        (Shape.leaves b v.2).map (fun p => (1 :: p.1, p.2))
  | .vec n a, v =>
      (List.finRange n).flatMap fun i => (Shape.leaves a (v i)).map fun p => (i.val :: p.1, p.2)

/-- The netlist of a circuit with input port `inName` and the generated output
bundle. -/
def Circuit.netlist {a b : Shape} (c : Circuit a b) (inName : String) :
    b.Val Net × NetlistState :=
  (c.gen 0 0 (Shape.portVal inName a [])).run {}

end Ruby
