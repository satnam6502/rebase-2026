import Ruby.Sorting.Networks
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases

/-!
# The zero–one principle, and networks permute their inputs

A network *sorts* when its output is `mergeSort` of its input. Two facts give
this for every comparator network in this library:

* **Sortedness, by the zero–one principle.** If a network commutes with every
  monotone map into `Bool` and sorts every vector of bits, it sorts every
  vector over any linear order (`zero_one`).
* **Permutation.** A network built from wiring and compare–exchange cells
  permutes its input (`IsPerm`).

A sorted permutation of a list is `mergeSort` of that list (`sorts_of`).
-/

namespace Ruby.Vec

variable {α : Type}

/-! ## The zero–one principle -/

/-- **The zero–one principle.** A network that commutes with monotone maps into
`Bool` and sorts every vector of bits sorts every vector. -/
theorem zero_one [LinearOrder α] {n : Nat} (F : Net α n) (F₂ : Net Bool n)
    (hcomm : ∀ g : α → Bool, Monotone g → Commutes g F F₂)
    (hsort : ∀ y, Monotone (F₂ y)) (x : Fin n → α) : Monotone (F x) := by
  intro i j hij
  by_contra h
  have hlt : F x j < F x i := lt_of_not_ge h
  let g : α → Bool := fun a => decide (F x i ≤ a)
  have hg : Monotone g := by
    intro a b hab
    by_cases ha : F x i ≤ a
    · have hb : F x i ≤ b := le_trans ha hab
      simp [g, ha, hb]
    · simp [g, ha]
  have hm := hsort (g ∘ x) hij
  rw [← hcomm g hg x] at hm
  have h1 : g (F x i) = true := by simp [g]
  have h2 : g (F x j) = false := by simp [g, not_le.mpr hlt]
  simp only [Function.comp_apply, h1, h2] at hm
  exact absurd hm (by decide)

/-! ## Networks permute their inputs -/

/-- The network rearranges its input. -/
def IsPerm {n : Nat} (F : Net α n) : Prop := ∀ x, (List.ofFn (F x)).Perm (List.ofFn x)

namespace IsPerm

theorem id' {n : Nat} : IsPerm (id : Net α n) := fun _ => List.Perm.refl _

theorem seq {n : Nat} {F G : Net α n} (hF : IsPerm F) (hG : IsPerm G) : IsPerm (F ⨾ G) :=
  fun x => (hG (F x)).trans (hF x)

/-- Reindexing each input by some permutation of the wires. -/
theorem of_perms {n : Nat} {F : Net α n} (h : ∀ x, ∃ σ : Equiv.Perm (Fin n), F x = x ∘ σ) :
    IsPerm F := fun x => by
  obtain ⟨σ, hσ⟩ := h x
  rw [hσ]
  exact Equiv.Perm.ofFn_comp_perm σ x

/-- Reindexing by a permutation of the wires. -/
theorem of_perm {n : Nat} {F : Net α n} (σ : Equiv.Perm (Fin n)) (h : ∀ x, F x = x ∘ σ) :
    IsPerm F := of_perms fun x => ⟨σ, h x⟩

theorem hrep {n : Nat} {F : Net α n} (hF : IsPerm F) : ∀ k, IsPerm (Vec.hrep k F)
  | 0 => id'
  | k + 1 => hF.seq (hrep hF k)

end IsPerm

theorem ofFn_append {m : Nat} (u v : Fin m → α) :
    List.ofFn (append u v) = List.ofFn u ++ List.ofFn v := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, append]
    by_cases hj : j < m
    · rw [List.getElem_append_left (by simpa using hj)]
      simp [hj]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hj]

theorem IsPerm.parl {m : Nat} {F G : Net α m} (hF : IsPerm F) (hG : IsPerm G) :
    IsPerm (Vec.parl F G) := by
  intro x
  conv_rhs => rw [← append_lo_hi x]
  simp only [Vec.parl, ofFn_append]
  exact (hF _).append (hG _)

theorem IsPerm.two {m : Nat} {F : Net α m} (hF : IsPerm F) : IsPerm (Vec.two F) := hF.parl hF

/-! ### Wirings are permutations -/

/-- Where `unriffle` takes output `j` from. -/
def unriffleIdx {m : Nat} (j : Fin (m * 2)) : Fin (m * 2) :=
  if h : j.val < m then ⟨2 * j, by omega⟩ else ⟨2 * (j - m) + 1, by omega⟩

/-- Where `riffle` takes output `j` from. -/
def riffleIdx {m : Nat} (j : Fin (m * 2)) : Fin (m * 2) :=
  if j.val % 2 = 0 then ⟨j / 2, by omega⟩ else ⟨m + j / 2, by omega⟩

theorem unriffleIdx_val {m : Nat} (j : Fin (m * 2)) :
    (unriffleIdx j).val = if j.val < m then 2 * j.val else 2 * (j.val - m) + 1 := by
  unfold unriffleIdx; split_ifs <;> rfl

theorem riffleIdx_val {m : Nat} (j : Fin (m * 2)) :
    (riffleIdx j).val = if j.val % 2 = 0 then j.val / 2 else m + j.val / 2 := by
  unfold riffleIdx; split_ifs <;> rfl

/-- `unriffle` as a permutation of wires. -/
def unrifflePerm (m : Nat) : Equiv.Perm (Fin (m * 2)) where
  toFun := unriffleIdx
  invFun := riffleIdx
  left_inv j := by
    apply Fin.ext; rw [riffleIdx_val, unriffleIdx_val]; split_ifs <;> omega
  right_inv j := by
    apply Fin.ext; rw [unriffleIdx_val, riffleIdx_val]; split_ifs <;> omega

theorem unriffle_eq_comp {m : Nat} (x : Fin (m * 2) → α) : unriffle x = x ∘ unriffleIdx := by
  funext j
  simp only [unriffle, append, Function.comp, unriffleIdx]
  split_ifs <;> rfl

theorem riffle_eq_comp {m : Nat} (x : Fin (m * 2) → α) : riffle x = x ∘ riffleIdx := by
  funext j
  simp only [riffle, interleave, Function.comp, riffleIdx]
  split_ifs <;> rfl

theorem IsPerm.unriffle {m : Nat} : IsPerm (Vec.unriffle : Net α (m * 2)) :=
  IsPerm.of_perm (unrifflePerm m) unriffle_eq_comp

theorem IsPerm.riffle {m : Nat} : IsPerm (Vec.riffle : Net α (m * 2)) :=
  IsPerm.of_perm (unrifflePerm m).symm riffle_eq_comp

theorem altIdx_val {m : Nat} (j : Fin (m * 2)) :
    (altIdx j).val = if (j.val / 2) % 2 = 1 then
      (if j.val % 2 = 0 then j.val + 1 else j.val - 1) else j.val := by
  unfold altIdx; split_ifs <;> rfl

theorem altIdx_altIdx {m : Nat} (j : Fin (m * 2)) : altIdx (altIdx j) = j := by
  apply Fin.ext; rw [altIdx_val, altIdx_val]; split_ifs <;> omega

theorem IsPerm.alt {m : Nat} : IsPerm (Vec.alt : Net α (m * 2)) :=
  IsPerm.of_perm (Function.Involutive.toPerm _ altIdx_altIdx) fun _ => rfl

theorem IsPerm.rev {n : Nat} : IsPerm (Vec.rev : Net α n) :=
  IsPerm.of_perm Fin.revPerm fun x => by
    funext i; simp only [Vec.rev, Function.comp, Fin.revPerm_apply]; congr 1; ext; simp; omega

theorem IsPerm.ilv {m : Nat} {F : Net α m} (hF : IsPerm F) : IsPerm (Vec.ilv F) :=
  (IsPerm.unriffle.seq hF.two).seq IsPerm.riffle

theorem IsPerm.vee {m : Nat} {F : Net α m} (hF : IsPerm F) : IsPerm (Vec.vee F) :=
  (IsPerm.alt.seq hF.ilv).seq IsPerm.alt

theorem IsPerm.que {m : Nat} {F : Net α (m * 2)} (hF : IsPerm F) : IsPerm (Vec.que F) :=
  (IsPerm.unriffle.ilv.seq hF.two).seq IsPerm.riffle.ilv

/-! ### Columns of compare–exchange cells are permutations -/

/-- A compare–exchange cell either passes its pair through or swaps it. -/
def SwapCell (f : Net α 2) : Prop := ∀ y, f y = y ∨ f y = rev y

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | _, h⟩
  · left; rfl
  · right; rfl
  · omega

theorem cmp_swapCell [LinearOrder α] : SwapCell (cmp : Net α 2) := by
  intro y
  by_cases h : y 0 ≤ y 1
  · left; funext i
    rcases fin2_cases i with rfl | rfl
    · simp [h]
    · simp [h]
  · right; funext i
    have h' : y 1 ≤ y 0 := le_of_lt (not_le.mp h)
    rcases fin2_cases i with rfl | rfl
    · simp [h', rev]
    · simp [h', rev]

/-- Swapping some pairs of a pairing is a permutation. -/
def condSwap {n : Nat} (p : Fin n → Fin n) (hp : ∀ j, p (p j) = j) (s : Fin n → Prop)
    [DecidablePred s] (hs : ∀ j, s (p j) ↔ s j) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun j => if s j then p j else j) (by
    intro j
    by_cases h : s j
    · have h' : s (p j) := (hs j).mpr h
      simp [h, h', hp]
    · simp [h])

theorem condSwap_apply {n : Nat} (p : Fin n → Fin n) (hp : ∀ j, p (p j) = j) (s : Fin n → Prop)
    [DecidablePred s] (hs : ∀ j, s (p j) ↔ s j) (j : Fin n) :
    condSwap p hp s hs j = if s j then p j else j := rfl

/-- The partner of a wire in its pair `(2 i, 2 i + 1)`. -/
def evensPartner {m : Nat} (j : Fin (m * 2)) : Fin (m * 2) :=
  if h : j.val % 2 = 0 then ⟨j + 1, by have := j.isLt; omega⟩ else ⟨j - 1, by omega⟩

theorem evensPartner_val {m : Nat} (j : Fin (m * 2)) :
    (evensPartner j).val = if j.val % 2 = 0 then j.val + 1 else j.val - 1 := by
  unfold evensPartner; split_ifs <;> rfl

theorem IsPerm.evens {m : Nat} {f : Net α 2} (hf : SwapCell f) :
    IsPerm (Vec.evens f : Net α (m * 2)) := by
  classical
  refine IsPerm.of_perms fun x => ?_
  let s : Fin (m * 2) → Prop := fun j => f (pairs x ⟨j / 2, by omega⟩) ≠ pairs x ⟨j / 2, by omega⟩
  have hp : ∀ j : Fin (m * 2), evensPartner (evensPartner j) = j := by
    intro j; apply Fin.ext; rw [evensPartner_val, evensPartner_val]; split_ifs <;> omega
  have hs : ∀ j, s (evensPartner j) ↔ s j := by
    intro j
    have : (evensPartner j).val / 2 = j.val / 2 := by
      rw [evensPartner_val]; split_ifs <;> omega
    simp only [s, this]
  refine ⟨condSwap evensPartner hp s hs, ?_⟩
  funext j
  simp only [Function.comp, condSwap_apply, Vec.evens, unpairs]
  by_cases h : s j
  · simp only [h, ↓reduceIte, (hf _).resolve_left h]
    simp only [Vec.rev, Vec.pairs]
    congr 1; apply Fin.ext; rw [evensPartner_val]; simp only; split_ifs <;> omega
  · simp only [h, ↓reduceIte, show f (pairs x ⟨j / 2, by omega⟩) = pairs x ⟨j / 2, by omega⟩ from
      not_not.mp h]
    simp only [Vec.pairs]
    congr 1; apply Fin.ext; simp only; omega

/-- The partner of a middle wire in its pair `(2 i + 1, 2 i + 2)`; the end
wires are their own partners. -/
def midPartner {m : Nat} (j : Fin (m * 2)) : Fin (m * 2) :=
  if h : IsEnd j then j
  else if j.val % 2 = 1 then ⟨j + 1, by unfold IsEnd at h; have := j.isLt; omega⟩
  else ⟨j - 1, by omega⟩

theorem midPartner_val {m : Nat} (j : Fin (m * 2)) :
    (midPartner j).val = if j.val = 0 ∨ j.val = m * 2 - 1 then j.val
      else if j.val % 2 = 1 then j.val + 1 else j.val - 1 := by
  unfold midPartner IsEnd
  by_cases h1 : j.val = 0 ∨ j.val = m * 2 - 1
  · simp only [h1, ↓reduceDIte, ↓reduceIte]
  · simp only [h1, ↓reduceDIte, ↓reduceIte]; split_ifs <;> rfl

theorem isEnd_midPartner {m : Nat} (j : Fin (m * 2)) : IsEnd (midPartner j) ↔ IsEnd j := by
  unfold IsEnd; rw [midPartner_val]; have := j.isLt; fin_omega

theorem midPair_midPartner {m : Nat} (x : Fin (m * 2) → α) (j : Fin (m * 2)) :
    midPair x (midPartner j) = midPair x j := by
  have h : ((midPartner j).val - 1) / 2 = (j.val - 1) / 2 := by
    rw [midPartner_val]; have := j.isLt; fin_omega
  funext b; simp only [midPair, h]

theorem IsPerm.midEvens {m : Nat} {f : Net α 2} (hf : SwapCell f) :
    IsPerm (Vec.midEvens f : Net α (m * 2)) := by
  classical
  refine IsPerm.of_perms fun x => ?_
  let s : Fin (m * 2) → Prop := fun j => ¬ IsEnd j ∧ f (midPair x j) ≠ midPair x j
  have hp : ∀ j : Fin (m * 2), midPartner (midPartner j) = j := by
    intro j; apply Fin.ext; rw [midPartner_val, midPartner_val]
    have := j.isLt
    fin_omega
  have hs : ∀ j, s (midPartner j) ↔ s j := by
    intro j; simp only [s, isEnd_midPartner, midPair_midPartner]
  refine ⟨condSwap midPartner hp s hs, ?_⟩
  funext j
  simp only [Function.comp, condSwap_apply, Vec.midEvens]
  by_cases hend : IsEnd j
  · have : ¬ s j := fun h => h.1 hend
    simp only [hend, this, ↓reduceIte]
  · by_cases h : f (midPair x j) = midPair x j
    · have : ¬ s j := fun hs => hs.2 h
      have hend' := hend
      unfold IsEnd at hend'
      simp only [hend, this, h, ↓reduceIte, midPair_of_not_end x j hend']
      congr 1; apply Fin.ext; simp only; have := j.isLt; omega
    · have hsj : s j := ⟨hend, h⟩
      have hend' := hend
      unfold IsEnd at hend'
      simp only [hend, hsj, ↓reduceIte, (hf _).resolve_left h, Vec.rev,
        midPair_of_not_end x j hend']
      congr 1; apply Fin.ext; simp only
      rw [midPartner_val]; have := j.isLt
      fin_omega

/-! ### Every network built from compare–exchange cells is a permutation -/

section
variable {f : Net α 2}

theorem IsPerm.bfly (hf : SwapCell f) : ∀ n, IsPerm (Vec.bfly f n)
  | 0 => id'
  | 1 => fun x => by
      rcases hf x with h | h
      · show (List.ofFn (f x)).Perm _; rw [h]
      · show (List.ofFn (f x)).Perm _; rw [h]; exact IsPerm.rev x
  | n + 2 => (IsPerm.bfly hf (n + 1)).ilv.seq (IsPerm.evens hf)

theorem IsPerm.cell (hf : SwapCell f) : IsPerm f := IsPerm.bfly hf 1

theorem IsPerm.mergeOE (hf : SwapCell f) : ∀ n, IsPerm (Vec.mergeOE f n)
  | 0 => id'
  | 1 => IsPerm.cell hf
  | n + 2 => (IsPerm.mergeOE hf (n + 1)).ilv.seq (IsPerm.midEvens hf)

theorem IsPerm.vfly (hf : SwapCell f) : ∀ n, IsPerm (Vec.vfly f n)
  | 0 => id'
  | 1 => IsPerm.cell hf
  | n + 2 => (IsPerm.vfly hf (n + 1)).vee.seq (IsPerm.evens hf)

theorem IsPerm.qfly (hf : SwapCell f) : ∀ n, IsPerm (Vec.qfly f n)
  | 0 => id'
  | 1 => IsPerm.cell hf
  | n + 2 => (IsPerm.qfly hf (n + 1)).que.seq (IsPerm.midEvens hf)

theorem IsPerm.mergeB (hf : SwapCell f) (n : Nat) : IsPerm (Vec.mergeB f n) :=
  (IsPerm.id'.parl IsPerm.rev).seq (IsPerm.bfly hf (n + 1))

theorem IsPerm.sortB (hf : SwapCell f) : ∀ n, IsPerm (Vec.sortB f n)
  | 0 => id'
  | n + 1 => ((IsPerm.sortB hf n).parl ((IsPerm.sortB hf n).seq IsPerm.rev)).seq
      (IsPerm.bfly hf (n + 1))

theorem IsPerm.sortOE (hf : SwapCell f) : ∀ n, IsPerm (Vec.sortOE f n)
  | 0 => id'
  | n + 1 => (IsPerm.sortOE hf n).two.seq (IsPerm.mergeOE hf (n + 1))

theorem IsPerm.sortV (hf : SwapCell f) (n : Nat) : IsPerm (Vec.sortV f n) :=
  (IsPerm.vfly hf n).hrep n

theorem IsPerm.sortQ (hf : SwapCell f) (n : Nat) : IsPerm (Vec.sortQ f n) :=
  (IsPerm.qfly hf n).hrep n

end

/-! ## Sorting -/

/-- `F` sorts: its output is `mergeSort` of its input. -/
def Sorts [LinearOrder α] {n : Nat} (F : Net α n) : Prop :=
  ∀ x, List.ofFn (F x) = (List.ofFn x).mergeSort (· ≤ ·)

/-- A network that permutes and always produces sorted output sorts. -/
theorem sorts_of [LinearOrder α] {n : Nat} {F : Net α n} (hp : IsPerm F)
    (hm : ∀ x, Monotone (F x)) : Sorts F := fun x =>
  List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr (hm x)) List.sortedLE_mergeSort
    ((hp x).trans (List.mergeSort_perm _ _).symm)

end Ruby.Vec
