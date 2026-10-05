import Ruby.Sorting
import Ruby.Sorter.Correctness
import Ruby.Sorter.Layout
import Ruby.NetlistLayout
import Ruby.NetlistSemantics

/-!
# The headline theorems

The results of this library, restated as `example`s so their exact statements
are in one place. Every statement is universally quantified over the degree
`n` (the sorters have `2 ^ n` inputs) and, for the hardware, over the word
width `4 k` (`k > 0`).
-/

namespace Ruby

open Vec Sorter Circuit

/-! ## Sorting networks: the four cores sort, and refine one another -/

example {α : Type} [LinearOrder α] (n : Nat) (x : Fin (2 ^ n) → α) :
    List.ofFn (sortB cmp n x) = (List.ofFn x).mergeSort (· ≤ ·) := sortB_sorts n x

example {α : Type} [LinearOrder α] (n : Nat) (x : Fin (2 ^ n) → α) :
    List.ofFn (sortOE cmp n x) = (List.ofFn x).mergeSort (· ≤ ·) := sortOE_sorts n x

example {α : Type} [LinearOrder α] (n : Nat) (x : Fin (2 ^ n) → α) :
    List.ofFn (sortV cmp n x) = (List.ofFn x).mergeSort (· ≤ ·) := sortV_sorts n x

example {α : Type} [LinearOrder α] (n : Nat) (x : Fin (2 ^ n) → α) :
    List.ofFn (sortQ cmp n x) = (List.ofFn x).mergeSort (· ≤ ·) := sortQ_sorts n x

/-- Bird–Meertens steps, for every symmetric two-input cell `f`. -/
example {α : Type} (f : Vec.Net α 2) (hf : Vec.Symm f) (n : Nat) :
    Vec.sortB f (n + 1) = Vec.two (Vec.sortB f n) ⨾ Vec.mergeB f n ∧
    Vec.vfly f (n + 1) = Vec.unriffle ⨾ Vec.mergeB f n ∧
    Vec.qfly f (n + 1) = Vec.unriffle ⨾ Vec.mergeOE f (n + 1) :=
  ⟨sortB_succ f n, vfly_eq hf n, qfly_eq hf n⟩

/-- The merging laws: Batcher's mergers agree on sorted halves, and `n + 1` passes
of `unriffle ⨾ merge` sort. -/
example {α : Type} [LinearOrder α] (n : Nat) (x : Fin (2 ^ (n + 1)) → α)
    (hx : HalvesSorted (m := 2 ^ n) x) : mergeB cmp n x = mergeOE cmp (n + 1) x :=
  merge_exchange n x hx

example {α : Type} [LinearOrder α] (n : Nat) :
    Sorts (hrep (n + 1) (Vec.unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) : Vec.Net α (2 ^ (n + 1))) :=
  periodicOE_sorts n

/-- The paper's lemma. -/
example {α : Type} {k : Nat} (g : Vec.Net α k) : que (ilv g) = ilv (ilv g) := que_ilv g

/-- The refinement chain sortB → sortOE → sortQ → sortV. -/
example {α : Type} [LinearOrder α] (n : Nat) :
    (Vec.sortB cmp n : Vec.Net α (2 ^ n)) = Vec.sortOE cmp n ∧
      (Vec.sortOE cmp n : Vec.Net α (2 ^ n)) = Vec.sortQ cmp n ∧
      (Vec.sortQ cmp n : Vec.Net α (2 ^ n)) = Vec.sortV cmp n :=
  sorter_refinement n

/-! ## Hardware: the circuits of Xilinx primitives sort, as pipelines -/

example (k n : Nat) (hk : 0 < k) (x : Fin (2 ^ n) → Fin (k * 4) → Bool) :
    values ((bitonicSorter k n).eval x) = (values x).mergeSort (· ≤ ·) :=
  bitonicSorter_sorts hk n x

example (k n : Nat) (hk : 0 < k) (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (Shape.sample ((bitonicSorter k n).evalS xs) (t + tri n)) =
      (values (Shape.sample xs t)).mergeSort (· ≤ ·) :=
  bitonicSorter_pipelined hk n xs t

example (k n : Nat) (hk : 0 < k) (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (Shape.sample ((periodicSorter k n).evalS xs) (t + n * n)) =
      (values (Shape.sample xs t)).mergeSort (· ≤ ·) :=
  periodicSorter_pipelined hk n xs t

/-! ## Layout: compact, non-overlapping, dense, and what is emitted -/

example (k n : Nat) :
    (bitonicSorter (k + 1) (n + 1)).size = (2 * tri (n + 1), 2 ^ n * (8 * (k + 1))) :=
  size_bitonicSorter k n

example (k n x y : Nat) : ((oddEvenSorter k n).sites x y).Nodup := nodup_oddEvenSorter k n x y

example (k n x y : Nat) :
    ∀ i < (bitonicSorter (k + 1) (n + 1)).size.1, ∀ j < (bitonicSorter (k + 1) (n + 1)).size.2,
      (x + i, y + j, Site.lut) ∈ (bitonicSorter (k + 1) (n + 1)).sites x y :=
  bitonicSorter_dense k n x y

example {a b : Shape} (c : Circuit a b) (x y : Nat) (v : a.Val Net) :
    EmitsSites (c.gen x y v) (c.sites x y) := Circuit.gen_sites c x y v

/-! ## The emitted netlist computes the verified function -/

example {a b : Shape} (c : Circuit a b) (port : String → List Nat → Bool) :
    b.map (Net.val (execAll ⟨fun _ => false, port⟩ (c.netlist "a").2.insts.toList))
        (c.netlist "a").1 =
      c.eval (a.map (Net.val ⟨fun _ => false, port⟩) (Shape.portVal "a" a [])) :=
  Circuit.netlist_correct c "a" port

end Ruby
