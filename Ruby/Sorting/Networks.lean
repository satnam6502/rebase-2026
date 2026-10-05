import Ruby.Vec
import Mathlib.Order.Lattice
import Mathlib.Order.MinMax

/-!
# Four sorter cores

K. Claessen, M. Sheeran and S. Singh, *The Design and Verification of a Sorter
Core* (CHARME 2001) build four sorters from a few connection patterns:

* `sortB`, Batcher's bitonic sorter, recursive;
* `sortOE`, Batcher's odd–even merge sorter, recursive;
* `sortV`, periodic: `n` copies of Dowd et al.'s balanced merger `vfly`;
* `sortQ`, periodic: `n` copies of Canfield and Williamson's merger `qfly`.

Here they are networks on `2 ^ n` wires, parameterised by the two-input cell
`f`. With the comparator `cmp` they sort; with the hardware two-sorter of
`Ruby.Sorters.Cell` they are the circuits that are laid out and emitted as
SystemVerilog.
-/

namespace Ruby.Vec

variable {α β : Type}

/-! ## The four mergers -/

/-- Batcher's bitonic merger: a butterfly on `2ⁿ` inputs. -/
def bfly (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | 1 => f
  | n + 2 => ilv (bfly f (n + 1)) ⨾ evens f

/-- Batcher's odd–even merger. Only the last column differs from `bfly`. -/
def mergeOE (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | 1 => f
  | n + 2 => ilv (mergeOE f (n + 1)) ⨾ midEvens f

/-- Dowd et al.'s balanced merger. -/
def vfly (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | 1 => f
  | n + 2 => vee (vfly f (n + 1)) ⨾ evens f

/-- Canfield and Williamson's merger. -/
def qfly (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | 1 => f
  | n + 2 => que (qfly f (n + 1)) ⨾ midEvens f

/-- Batcher's bitonic merger read as a merger of two sorted halves: reverse the
second half, then run the butterfly. -/
def mergeB (f : Net α 2) (n : Nat) : Net α (2 ^ (n + 1)) := parl id rev ⨾ bfly f (n + 1)

/-! ## The four sorters -/

/-- Batcher's bitonic sorter. -/
def sortB (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | n + 1 => parl (sortB f n) (sortB f n ⨾ rev) ⨾ bfly f (n + 1)

/-- Batcher's odd–even merge sorter. -/
def sortOE (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | n + 1 => two (sortOE f n) ⨾ mergeOE f (n + 1)

/-- A periodic sorter: `n` balanced mergers in series. -/
def sortV (f : Net α 2) (n : Nat) : Net α (2 ^ n) := hrep n (vfly f n)

/-- A periodic sorter: `n` Canfield–Williamson mergers in series. -/
def sortQ (f : Net α 2) (n : Nat) : Net α (2 ^ n) := hrep n (qfly f n)

/-! ## The comparator -/

/-- The comparator: the minimum to wire `0`, the maximum to wire `1`. -/
def cmp [LinearOrder α] : Net α 2 := fun x i =>
  if i.val = 0 then min (x 0) (x 1) else max (x 0) (x 1)

@[simp] theorem cmp_zero [LinearOrder α] (x : Fin 2 → α) : cmp x 0 = min (x 0) (x 1) := rfl
@[simp] theorem cmp_one [LinearOrder α] (x : Fin 2 → α) : cmp x 1 = max (x 0) (x 1) := rfl

/-- A two-input cell that does not care which input is which. -/
def Symm (f : Net α 2) : Prop := ∀ x, f (rev x) = f x

theorem cmp_symm [LinearOrder α] : Symm (cmp : Net α 2) := by
  intro x; funext i
  simp only [cmp, rev]
  split_ifs
  · exact min_comm _ _
  · exact max_comm _ _

/-- A monotone map commutes with the comparator. -/
theorem Commutes.cmp [LinearOrder α] [LinearOrder β] {g : α → β} (hg : Monotone g) :
    Commutes g (Vec.cmp : Net α 2) Vec.cmp := by
  intro x; funext i
  simp only [Function.comp, Vec.cmp]
  split_ifs
  · exact hg.map_min
  · exact hg.map_max

/-! ## Elementwise maps commute with every network -/

namespace Commutes

variable {g : α → β} {f : Net α 2} {f' : Net β 2}

theorem bfly (hf : Commutes g f f') : ∀ n, Commutes g (Vec.bfly f n) (Vec.bfly f' n)
  | 0 => id'
  | 1 => hf
  | n + 2 => (bfly hf (n + 1)).ilv.seq hf.evens

theorem mergeOE (hf : Commutes g f f') : ∀ n, Commutes g (Vec.mergeOE f n) (Vec.mergeOE f' n)
  | 0 => id'
  | 1 => hf
  | n + 2 => (mergeOE hf (n + 1)).ilv.seq hf.midEvens

theorem vfly (hf : Commutes g f f') : ∀ n, Commutes g (Vec.vfly f n) (Vec.vfly f' n)
  | 0 => id'
  | 1 => hf
  | n + 2 => (vfly hf (n + 1)).vee.seq hf.evens

theorem qfly (hf : Commutes g f f') : ∀ n, Commutes g (Vec.qfly f n) (Vec.qfly f' n)
  | 0 => id'
  | 1 => hf
  | n + 2 => (qfly hf (n + 1)).que.seq hf.midEvens

theorem mergeB (hf : Commutes g f f') (n : Nat) :
    Commutes g (Vec.mergeB f n) (Vec.mergeB f' n) :=
  (id'.parl rev).seq (hf.bfly (n + 1))

theorem sortB (hf : Commutes g f f') : ∀ n, Commutes g (Vec.sortB f n) (Vec.sortB f' n)
  | 0 => id'
  | n + 1 => ((sortB hf n).parl ((sortB hf n).seq rev)).seq (hf.bfly (n + 1))

theorem sortOE (hf : Commutes g f f') : ∀ n, Commutes g (Vec.sortOE f n) (Vec.sortOE f' n)
  | 0 => id'
  | n + 1 => (sortOE hf n).two.seq (hf.mergeOE (n + 1))

theorem sortV (hf : Commutes g f f') (n : Nat) : Commutes g (Vec.sortV f n) (Vec.sortV f' n) :=
  (hf.vfly n).hrep n

theorem sortQ (hf : Commutes g f f') (n : Nat) : Commutes g (Vec.sortQ f n) (Vec.sortQ f' n) :=
  (hf.qfly n).hrep n

end Commutes

end Ruby.Vec
