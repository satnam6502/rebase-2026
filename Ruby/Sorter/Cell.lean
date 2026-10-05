import Ruby.Combinators

/-!
# The two-sorter cell, from Xilinx 7-series primitives

A port of the pipelined two-sorter of `xilinx-lava` (`twoSorterRegL`), for
unsigned words of `4 k` bits. Each output word has its own half of the cell:

```
        X0 (one slice column)                 X1
  max:  CARRY4 chain, b ≥ a (k slices)        LUT3 muxes + FDCEs (k slices)
  min:  CARRY4 chain, a ≥ b (k slices)        LUT3 muxes + FDCEs (k slices)
```

* The comparator is Ruby's `col` of `k` CARRY4 tiles with the carry running up
  the dedicated carry chain. In each tile, LUTs A–D compute `S = a XNOR b`, the
  CARRY4 takes `DI = a`, and the carry out of the top is `1` exactly when
  `a ≥ b` (the subtraction `a + ~b + 1` does not borrow).
* The selection is a column of `LUT3` multiplexers (`INIT = 8'hE4`) overlaid with
  the `FDCE` registers they drive, so each LUT and its flip-flop share a slice.

The cell is `2` slices wide and `2 k` slices high; every path through it has
exactly one register.
-/

namespace Ruby.Sorter

open Shape Circuit

/-! ## Primitive cells -/

/-- `I0 XNOR I1`, the propagate signal of a subtraction (`LUT2`, `INIT = 4'h9`). -/
def xnorLut : Circuit (.word 2) .bit := prim (.lut 2 fun v => v 0 == v 1)

/-- `I0 ? I2 : I1`, a 2:1 multiplexer (`LUT3`, `INIT = 8'hE4`). -/
def muxLut : Circuit (.word 3) .bit := prim (.lut 3 fun v => if v 0 then v 2 else v 1)

/-- A register (`FDCE` with `CE = 1` and `CLR` driven by reset). -/
def reg : Circuit .bit .bit := prim .fdce

/-- A vector of two values. -/
def pair2 {β : Type} (u v : β) : Fin 2 → β := fun j => if j.val = 0 then u else v

/-- A vector of three values. -/
def triple {β : Type} (u v w : β) : Fin 3 → β := fun j =>
  if j.val = 0 then u else if j.val = 1 then v else w

/-! ## The comparator -/

/-- The state of a carry chain between slices: `(CI, CYINIT)`. -/
abbrev CarryState : Shape := .pair .bit .bit

/-- Four bits of each operand. -/
abbrev Chunk : Shape := .pair (.word 4) (.word 4)

/-- One slice of the comparator: LUTs A–D compute `S = a XNOR b` and the
CARRY4 on top of them propagates the carry. -/
def geTile : Circuit (.pair CarryState Chunk) (.pair (.word 4) CarryState) :=
  wire ⟨fun _ v => (v.1, (v.2.1, fun i => pair2 (v.2.1 i) (v.2.2 i))), by
      intros; refine Prod.ext rfl (Prod.ext rfl ?_); funext i j
      simp only [Shape.map_vec, Shape.map_pair, pair2]; split_ifs <;> rfl⟩ >->
    (snd (snd (map 4 xnorLut)) >|> prim .carry4) >->
    wire ⟨fun k v => (v.1, (v.2 3, k false)), by intros; rfl⟩

/-- Split a `4 k`-bit word into `k` four-bit chunks, least significant first. -/
def chunk {β : Type} {k : Nat} (v : Fin (k * 4) → β) (j : Fin k) : Fin 4 → β :=
  fun i => v ⟨4 * j.val + i.val, by have := j.isLt; have := i.isLt; omega⟩

/-- `a ≥ b` on `4 k`-bit unsigned words: a carry chain of `k` CARRY4 slices,
started with `CI = 0`, `CYINIT = 1`. -/
def geC (k : Nat) : Circuit (.pair (.word (k * 4)) (.word (k * 4))) .bit :=
  wire ⟨fun c v => ((c false, c true), fun j => (chunk v.1 j, chunk v.2 j)), by intros; rfl⟩ >->
    col k geTile >->
    wire ⟨fun _ v => v.2.1, by intros; rfl⟩

/-! ## The cell -/

/-- Select `b` when the select line is set, then register: a column of LUT3
multiplexers overlaid with the FDCEs they drive. -/
def muxReg (w : Nat) : Circuit (.pair .bit (.pair (.word w) (.word w))) (.word w) :=
  wire ⟨fun _ v => fun i => triple v.1 (v.2.1 i) (v.2.2 i), by
      intros; funext i j; simp only [Shape.map_vec, Shape.map_pair, triple]; split_ifs <;> rfl⟩ >->
    (map w muxLut >|> map w reg)

/-- `min (a, b)`, registered: `a ≥ b` selects `b`. -/
def halfMin (k : Nat) : Circuit (.pair (.word (k * 4)) (.word (k * 4))) (.word (k * 4)) :=
  wire Wiring.fork >-> fst (geC k) >-> muxReg (k * 4)

/-- `max (a, b)`, registered: `b ≥ a` selects `b`. -/
def halfMax (k : Nat) : Circuit (.pair (.word (k * 4)) (.word (k * 4))) (.word (k * 4)) :=
  wire ⟨fun _ v => ((v.2, v.1), v), by intros; rfl⟩ >-> fst (geC k) >-> muxReg (k * 4)

/-- **The pipelined two-sorter** on `4 k`-bit words: the minimum half below the
maximum half. -/
def twoSorter (k : Nat) : Circuit (.vec 2 (.word (k * 4))) (.vec 2 (.word (k * 4))) :=
  wire ⟨fun _ v => ((v 0, v 1), (v 0, v 1)), by intros; rfl⟩ >->
    (halfMin k ‖ halfMax k) >->
    wire ⟨fun _ v => pair2 v.1 v.2, by
      intros; funext j; simp only [Shape.map_vec, Shape.map_pair, pair2]; split_ifs <;> rfl⟩

/-- A registered word: the delay that keeps the bypassed wires of the odd–even
middle column in step with the cells. -/
def delayW (w : Nat) : Circuit (.word w) (.word w) := map w reg

/-! ## The sorters, in hardware -/

/-- Batcher's bitonic sorter of `2 ^ n` words of `4 k` bits. -/
def bitonicSorter (k n : Nat) := sortB (twoSorter k) n

/-- Batcher's odd–even merge sorter of `2 ^ n` words of `4 k` bits. -/
def oddEvenSorter (k n : Nat) := sortOE (twoSorter k) (delayW (k * 4)) n

/-- The periodic balanced sorter of `2 ^ n` words of `4 k` bits. -/
def balancedSorter (k n : Nat) := sortV (twoSorter k) n

/-- The periodic Canfield–Williamson sorter of `2 ^ n` words of `4 k` bits. -/
def periodicSorter (k n : Nat) := sortQ (twoSorter k) (delayW (k * 4)) n

end Ruby.Sorter
