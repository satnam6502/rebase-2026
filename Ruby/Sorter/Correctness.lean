import Ruby.Sorter.CellProof
import Ruby.Latency

/-!
# The hardware sorters sort, at every degree and word width

For words of `4 k` bits (`k > 0`) and `2 ^ n` inputs, each of the four sorter
circuits built from Xilinx primitives:

* **sorts combinationally**: the decoded outputs are `mergeSort` of the decoded
  inputs (`bitonicSorter_sorts`, …);
* **is a balanced pipeline**: every path carries the same number of registers
  (`bitonicSorter_latency`, …), `n (n + 1) / 2` for the recursive sorters and
  `n²` for the periodic ones;
* hence, **as a synchronous circuit**, the outputs at cycle `t + latency` are
  the inputs at cycle `t`, sorted (`bitonicSorter_pipelined`, …).

All statements are universally quantified over the degree `n`, the word width
`k` and the inputs.
-/

namespace Ruby.Sorter

open Shape Circuit Vec

/-! ## Latency of the cell -/

theorem latency_geTile : geTile.latency = some 0 := rfl

theorem latency_geC (k : Nat) : (geC k).latency = some 0 :=
  latency_wire_seq _ (latency_seq_wire _ (latency_col latency_geTile))

theorem latency_muxReg (w : Nat) : (muxReg w).latency = some 1 := rfl

theorem latency_halfMin (k : Nat) : (halfMin k).latency = some 1 :=
  (latency_wire_seq _ (latency_seq (latency_fst (latency_geC k)) (latency_muxReg _))).trans
    (by simp)

theorem latency_halfMax (k : Nat) : (halfMax k).latency = some 1 :=
  (latency_wire_seq _ (latency_seq (latency_fst (latency_geC k)) (latency_muxReg _))).trans
    (by simp)

/-- Every path through the two-sorter cell carries exactly one register. -/
theorem latency_twoSorter (k : Nat) : (twoSorter k).latency = some 1 :=
  latency_wire_seq _ (latency_seq_wire _ (latency_par (latency_halfMin k) (latency_halfMax k)))

theorem latency_delayW (w : Nat) : (delayW w).latency = some 1 := rfl

/-! ## Combinational correctness -/

/-- The decoded words of a vector. -/
def values {N w : Nat} (x : Fin N → Fin w → Bool) : List Nat := List.ofFn fun i => wordVal (x i)

variable {k : Nat}

/-- **The hardware bitonic sorter sorts**, for every degree `n`. -/
theorem bitonicSorter_sorts (hk : 0 < k) (n : Nat) (x : Fin (2 ^ n) → Fin (k * 4) → Bool) :
    values ((bitonicSorter k n).eval x) = (values x).mergeSort (· ≤ ·) := by
  have hc := Commutes.sortB (twoSorter_commutes hk) n x
  unfold values bitonicSorter
  rw [eval_sortB]
  exact (congrArg List.ofFn hc).trans (sortB_sorts n (wordVal ∘ x))

/-- **The hardware odd–even merge sorter sorts**, for every degree `n`. -/
theorem oddEvenSorter_sorts (hk : 0 < k) (n : Nat) (x : Fin (2 ^ n) → Fin (k * 4) → Bool) :
    values ((oddEvenSorter k n).eval x) = (values x).mergeSort (· ≤ ·) := by
  have hc := Commutes.sortOE (twoSorter_commutes hk) n x
  unfold values oddEvenSorter
  rw [eval_sortOE (eval_delayW _)]
  exact (congrArg List.ofFn hc).trans (sortOE_sorts n (wordVal ∘ x))

/-- **The hardware periodic balanced sorter sorts**, for every degree `n`. -/
theorem balancedSorter_sorts (hk : 0 < k) (n : Nat) (x : Fin (2 ^ n) → Fin (k * 4) → Bool) :
    values ((balancedSorter k n).eval x) = (values x).mergeSort (· ≤ ·) := by
  have hc := Commutes.sortV (twoSorter_commutes hk) n x
  unfold values balancedSorter
  rw [eval_sortV]
  exact (congrArg List.ofFn hc).trans (sortV_sorts n (wordVal ∘ x))

/-- **The hardware periodic Canfield–Williamson sorter sorts**, for every degree
`n`. -/
theorem periodicSorter_sorts (hk : 0 < k) (n : Nat) (x : Fin (2 ^ n) → Fin (k * 4) → Bool) :
    values ((periodicSorter k n).eval x) = (values x).mergeSort (· ≤ ·) := by
  have hc := Commutes.sortQ (twoSorter_commutes hk) n x
  unfold values periodicSorter
  rw [eval_sortQ (eval_delayW _)]
  exact (congrArg List.ofFn hc).trans (sortQ_sorts n (wordVal ∘ x))

/-! ## Latency -/

theorem bitonicSorter_latency (k n : Nat) : (bitonicSorter k n).latency = some (tri n) :=
  (latency_sortB (latency_twoSorter k) n).trans (by simp)

theorem oddEvenSorter_latency (k n : Nat) : (oddEvenSorter k n).latency = some (tri n) :=
  (latency_sortOE (latency_twoSorter k) (latency_delayW _) n).trans (by simp)

theorem balancedSorter_latency (k n : Nat) : (balancedSorter k n).latency = some (n * n) :=
  (latency_sortV (latency_twoSorter k) n).trans (by simp)

theorem periodicSorter_latency (k n : Nat) : (periodicSorter k n).latency = some (n * n) :=
  (latency_sortQ (latency_twoSorter k) (latency_delayW _) n).trans (by simp)

/-! ## Synchronous correctness -/

/-- **The pipelined hardware bitonic sorter**: the words leaving it at cycle
`t + n (n + 1) / 2` are the words that entered at cycle `t`, sorted. -/
theorem bitonicSorter_pipelined (hk : 0 < k) (n : Nat)
    (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (sample ((bitonicSorter k n).evalS xs) (t + tri n)) =
      (values (sample xs t)).mergeSort (· ≤ ·) := by
  rw [evalS_sample _ _ (bitonicSorter_latency k n)]
  exact bitonicSorter_sorts hk n _

theorem oddEvenSorter_pipelined (hk : 0 < k) (n : Nat)
    (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (sample ((oddEvenSorter k n).evalS xs) (t + tri n)) =
      (values (sample xs t)).mergeSort (· ≤ ·) := by
  rw [evalS_sample _ _ (oddEvenSorter_latency k n)]
  exact oddEvenSorter_sorts hk n _

theorem balancedSorter_pipelined (hk : 0 < k) (n : Nat)
    (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (sample ((balancedSorter k n).evalS xs) (t + n * n)) =
      (values (sample xs t)).mergeSort (· ≤ ·) := by
  rw [evalS_sample _ _ (balancedSorter_latency k n)]
  exact balancedSorter_sorts hk n _

theorem periodicSorter_pipelined (hk : 0 < k) (n : Nat)
    (xs : (Shape.vec (2 ^ n) (.word (k * 4))).Val Stream) (t : Nat) :
    values (sample ((periodicSorter k n).evalS xs) (t + n * n)) =
      (values (sample xs t)).mergeSort (· ≤ ·) := by
  rw [evalS_sample _ _ (periodicSorter_latency k n)]
  exact periodicSorter_sorts hk n _

end Ruby.Sorter
