import Ruby.Sorting.ZeroOne
import Mathlib.Tactic.IntervalCases

/-!
# Batcher's mergers merge, at every size

On bits, a sorted vector of length `N` with `a` ones is `ind (N - a) N`: the
ones occupy a final segment. The bitonic merger's butterfly sorts any bit
vector whose ones form one segment `ind p q` (`bfly_ind`); hence the bitonic
merger `mergeB` merges two sorted halves (`mergeB_ind`). The odd–even merger
merges two sorted halves too (`mergeOE_ind`). Both proofs are inductions on the
degree `n`, through the `ilv` recursion of the networks.

From these, `sortB` and `sortOE` sort every bit vector, and by the zero–one
principle every vector over a linear order.
-/

namespace Ruby.Vec

variable {α : Type}

/-! ## Bit vectors with one segment of ones -/

/-- The bit vector with ones exactly at the positions `p ≤ i < q`. -/
def ind {N : Nat} (p q : Nat) : Fin N → Bool := fun i => decide (p ≤ i.val ∧ i.val < q)

theorem min_bool (a b : Bool) : min a b = (a && b) := by cases a <;> cases b <;> rfl

theorem max_bool (a b : Bool) : max a b = (a || b) := by cases a <;> cases b <;> rfl

theorem decide_and_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem decide_or_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- A final segment of ones is sorted. -/
theorem monotone_ind {N : Nat} (a : Nat) : Monotone (ind (N := N) (N - a) N) := by
  intro i j hij
  have hij' : i.val ≤ j.val := hij
  by_cases h : N - a ≤ i.val
  · have hj : N - a ≤ j.val := le_trans h hij'
    simp [ind, h, hj, i.isLt, j.isLt]
  · simp [ind, h]

/-- A sorted bit vector is a final segment of ones. -/
theorem eq_ind_of_monotone {N : Nat} (y : Fin N → Bool) (hy : Monotone y) :
    ∃ a ≤ N, y = ind (N - a) N := by
  classical
  let P : Nat → Prop := fun k => k = N ∨ ∃ h : k < N, y ⟨k, h⟩ = true
  have hex : ∃ k, P k := ⟨N, Or.inl rfl⟩
  let p := Nat.find hex
  have hpN : p ≤ N := Nat.find_min' hex (Or.inl rfl)
  refine ⟨N - p, by omega, ?_⟩
  funext j
  have hj := j.isLt
  simp only [ind, show N - (N - p) = p by omega]
  by_cases hyj : y j = true
  · rw [hyj]; symm; simp only [decide_eq_true_eq]
    exact ⟨Nat.find_min' hex (Or.inr ⟨j.isLt, hyj⟩), hj⟩
  · have hyj' : y j = false := by simpa using hyj
    rw [hyj']; symm; simp only [decide_eq_false_iff_not, not_and, not_lt]
    intro hpj
    exfalso
    rcases Nat.find_spec hex with h | ⟨hp, hyp⟩
    · omega
    · have := hy (show (⟨p, hp⟩ : Fin N) ≤ j from hpj)
      rw [hyp, hyj'] at this
      exact absurd this (by decide)

/-! ## Wiring of segments -/

theorem evensIdx_ind {m : Nat} (p q : Nat) :
    evensIdx (ind (N := m * 2) p q) = ind ((p + 1) / 2) ((q + 1) / 2) := by
  funext i; simp only [evensIdx, ind]; apply decide_eq_decide.mpr; omega

theorem oddsIdx_ind {m : Nat} (p q : Nat) :
    oddsIdx (ind (N := m * 2) p q) = ind (p / 2) (q / 2) := by
  funext i; simp only [oddsIdx, ind]; apply decide_eq_decide.mpr; omega

theorem rev_ind_final {M : Nat} (b : Nat) (hb : b ≤ M) :
    rev (ind (N := M) (M - b) M) = ind 0 b := by
  funext i; simp only [rev, ind]; apply decide_eq_decide.mpr; have := i.isLt; omega

theorem append_ind {M : Nat} (a b : Nat) (ha : a ≤ M) (_hb : b ≤ M) :
    append (ind (N := M) (M - a) M) (ind 0 b) = ind (M - a) (M + b) := by
  funext j; simp only [append, ind]; split_ifs <;> (apply decide_eq_decide.mpr; omega)

theorem append_ind_ind {M : Nat} (a b : Nat) :
    append (ind (N := M) (M - a) M) (ind (M - b) M) =
      fun j : Fin (M * 2) => decide (j.val < M ∧ M - a ≤ j.val ∨ M ≤ j.val ∧ M - b ≤ j.val - M) := by
  funext j; simp only [append, ind]; split_ifs <;> (apply decide_eq_decide.mpr; omega)

theorem evensIdx_append {k : Nat} (u v : Fin (k * 2) → α) :
    evensIdx (m := k * 2) (append u v) = append (evensIdx u) (evensIdx v) := by
  funext i; simp only [evensIdx, append]
  split_ifs <;> first | omega | rfl | (congr 1; apply Fin.ext; simp only; omega)

theorem oddsIdx_append {k : Nat} (u v : Fin (k * 2) → α) :
    oddsIdx (m := k * 2) (append u v) = append (oddsIdx u) (oddsIdx v) := by
  funext i; simp only [oddsIdx, append]
  split_ifs <;> first | omega | rfl | (congr 1; apply Fin.ext; simp only; omega)

/-! ## The butterfly sorts a segment of ones -/

theorem evens_interleave_apply {M : Nat} (f : Net α 2) (u v : Fin M → α) (j : Fin (M * 2)) :
    evens f (interleave u v) j =
      f (fun b => if b.val = 0 then u ⟨j / 2, by omega⟩ else v ⟨j / 2, by omega⟩)
        ⟨j % 2, by omega⟩ := by
  simp only [evens_apply]
  congr 1; funext b
  have := b.isLt
  simp only [interleave]
  split_ifs <;> first | omega | (congr 1; apply Fin.ext; simp only; omega)

/-- The last column of the butterfly merges two interleaved sorted vectors
whose numbers of ones differ by at most one. -/
theorem evens_cmp_interleave {M : Nat} (e o : Nat) (he : e ≤ M) (ho : o ≤ M)
    (h1 : e ≤ o + 1) (h2 : o ≤ e + 1) :
    evens (m := M) cmp (interleave (ind (N := M) (M - e) M) (ind (M - o) M)) =
      ind (M * 2 - (e + o)) (M * 2) := by
  funext j
  have hj := j.isLt
  rw [evens_interleave_apply]
  by_cases hpar : j.val % 2 = 0
  · have : (⟨j.val % 2, by omega⟩ : Fin 2) = 0 := Fin.ext hpar
    rw [this, cmp_zero]
    simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, ind, min_bool, decide_and_decide,
      Nat.one_ne_zero]
    apply decide_eq_decide.mpr; omega
  · have : (⟨j.val % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
    rw [this, cmp_one]
    simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, ind, max_bool, decide_or_decide,
      Nat.one_ne_zero]
    apply decide_eq_decide.mpr; omega

/-- **The bitonic merger's butterfly sorts a segment of ones**, at every degree. -/
theorem bfly_ind : ∀ (n p q : Nat), p ≤ q → q ≤ 2 ^ n →
    bfly cmp n (ind p q) = ind (2 ^ n - (q - p)) (2 ^ n)
  | 0, p, q, hpq, hq => by
      funext i; have := i.isLt
      simp only [bfly, id, ind]; apply decide_eq_decide.mpr; simp at hq this ⊢; omega
  | 1, p, q, hpq, hq => by
      funext i
      simp only [Nat.pow_one] at hq
      rcases fin2_cases i with rfl | rfl <;>
        simp only [bfly, cmp_zero, cmp_one, ind, min_bool, max_bool, decide_and_decide,
          decide_or_decide] <;> apply decide_eq_decide.mpr <;> simp <;> omega
  | n + 2, p, q, hpq, hq => by
      have hM : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := Nat.pow_succ 2 (n + 1)
      change evens (m := 2 ^ (n + 1)) cmp (ilv (bfly cmp (n + 1)) (ind (N := 2 ^ (n + 1) * 2) p q)) =
        ind (N := 2 ^ (n + 1) * 2) (2 ^ (n + 2) - (q - p)) (2 ^ (n + 2))
      rw [ilv_apply, evensIdx_ind, oddsIdx_ind,
        bfly_ind (n + 1) _ _ (by omega) (by omega), bfly_ind (n + 1) _ _ (by omega) (by omega),
        evens_cmp_interleave _ _ (by omega) (by omega) (by omega) (by omega), hM]
      congr 2; omega

/-- **Batcher's bitonic merger merges two sorted halves**, at every degree. -/
theorem mergeB_ind (n a b : Nat) (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    mergeB cmp n (append (ind (N := 2 ^ n) (2 ^ n - a) (2 ^ n)) (ind (2 ^ n - b) (2 ^ n))) =
      ind (2 ^ (n + 1) - (a + b)) (2 ^ (n + 1)) := by
  change bfly cmp (n + 1) (parl (m := 2 ^ n) id rev
    (append (ind (N := 2 ^ n) (2 ^ n - a) (2 ^ n)) (ind (2 ^ n - b) (2 ^ n)))) = _
  rw [parl_append, id, rev_ind_final b hb, append_ind a b ha hb]
  have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
  refine (bfly_ind (n + 1) (2 ^ n - a) (2 ^ n + b) (by omega) (by omega)).trans ?_
  congr 1; omega

/-! ## The odd–even merger merges -/

theorem midEvens_interleave_apply {M : Nat} (f : Net α 2) (u v : Fin M → α) (j : Fin (M * 2))
    (hj : ¬ IsEnd j) :
    midEvens f (interleave u v) j =
      f (fun b => if b.val = 0 then v ⟨(j - 1) / 2, by unfold IsEnd at hj; omega⟩
        else u ⟨(j - 1) / 2 + 1, by unfold IsEnd at hj; omega⟩) ⟨(j - 1) % 2, by omega⟩ := by
  have hj' := hj
  unfold IsEnd at hj'
  simp only [midEvens, hj, ↓reduceIte]
  congr 1; funext b
  have := b.isLt
  rw [midPair_of_not_end _ _ hj']
  simp only [interleave]
  split_ifs <;> first | omega | (congr 1; apply Fin.ext; simp only; omega)

/-- The last column of the odd–even merger merges two interleaved sorted vectors
when the odd one has between zero and two more ones than the even one. -/
theorem midEvens_cmp_interleave {M : Nat} (e o : Nat) (he : e ≤ M) (ho : o ≤ M)
    (h1 : e ≤ o) (h2 : o ≤ e + 2) :
    midEvens (m := M) cmp (interleave (ind (N := M) (M - e) M) (ind (M - o) M)) =
      ind (M * 2 - (e + o)) (M * 2) := by
  funext j
  have hj := j.isLt
  by_cases hend : IsEnd j
  · have hend' := hend
    unfold IsEnd at hend'
    simp only [midEvens, hend, ↓reduceIte, interleave, ind]
    split_ifs <;> (apply decide_eq_decide.mpr; omega)
  · have hend' := hend
    unfold IsEnd at hend'
    rw [midEvens_interleave_apply _ _ _ _ hend]
    by_cases hpar : (j.val - 1) % 2 = 0
    · have : (⟨(j.val - 1) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext hpar
      rw [this, cmp_zero]
      simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, ind, min_bool, decide_and_decide,
        Nat.one_ne_zero]
      apply decide_eq_decide.mpr; omega
    · have : (⟨(j.val - 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp; omega)
      rw [this, cmp_one]
      simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, ind, max_bool, decide_or_decide,
        Nat.one_ne_zero]
      apply decide_eq_decide.mpr; omega

/-- **Batcher's odd–even merger merges two sorted halves**, at every degree. -/
theorem mergeOE_ind : ∀ (n a b : Nat), a ≤ 2 ^ n → b ≤ 2 ^ n →
    mergeOE cmp (n + 1) (append (ind (N := 2 ^ n) (2 ^ n - a) (2 ^ n)) (ind (2 ^ n - b) (2 ^ n))) =
      ind (2 ^ (n + 1) - (a + b)) (2 ^ (n + 1))
  | 0, a, b, ha, hb => by
      simp only [Nat.pow_zero] at ha hb
      funext i
      interval_cases a <;> interval_cases b <;> rcases fin2_cases i with rfl | rfl <;> decide
  | n + 1, a, b, ha, hb => by
      have hK : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      have hK2 : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := Nat.pow_succ 2 (n + 1)
      change midEvens (m := 2 ^ (n + 1)) cmp (ilv (mergeOE cmp (n + 1))
          (append (m := 2 ^ (n + 1)) (ind (N := 2 ^ (n + 1)) (2 ^ (n + 1) - a) (2 ^ (n + 1)))
            (ind (N := 2 ^ (n + 1)) (2 ^ (n + 1) - b) (2 ^ (n + 1))))) = _
      have eA : ∀ (u v : Fin (2 ^ (n + 1)) → Bool),
          evensIdx (m := 2 ^ (n + 1)) (append (m := 2 ^ (n + 1)) u v) =
            append (m := 2 ^ n) (evensIdx (m := 2 ^ n) u) (evensIdx (m := 2 ^ n) v) :=
        fun u v => evensIdx_append (k := 2 ^ n) u v
      have oA : ∀ (u v : Fin (2 ^ (n + 1)) → Bool),
          oddsIdx (m := 2 ^ (n + 1)) (append (m := 2 ^ (n + 1)) u v) =
            append (m := 2 ^ n) (oddsIdx (m := 2 ^ n) u) (oddsIdx (m := 2 ^ n) v) :=
        fun u v => oddsIdx_append (k := 2 ^ n) u v
      have eI : ∀ p q, evensIdx (m := 2 ^ n) (ind (N := 2 ^ (n + 1)) p q) =
          ind ((p + 1) / 2) ((q + 1) / 2) := fun p q => evensIdx_ind (m := 2 ^ n) p q
      have oI : ∀ p q, oddsIdx (m := 2 ^ n) (ind (N := 2 ^ (n + 1)) p q) =
          ind (p / 2) (q / 2) := fun p q => oddsIdx_ind (m := 2 ^ n) p q
      rw [ilv_apply, eA, oA, eI, eI, oI, oI]
      have hE : ∀ c, c ≤ 2 ^ (n + 1) →
          ind (N := 2 ^ n) ((2 ^ (n + 1) - c + 1) / 2) ((2 ^ (n + 1) + 1) / 2) =
            ind (2 ^ n - c / 2) (2 ^ n) := by
        intro c hc; congr 1 <;> omega
      have hO : ∀ c, c ≤ 2 ^ (n + 1) →
          ind (N := 2 ^ n) ((2 ^ (n + 1) - c) / 2) (2 ^ (n + 1) / 2) =
            ind (2 ^ n - (c + 1) / 2) (2 ^ n) := by
        intro c hc; congr 1 <;> omega
      rw [hE a ha, hE b hb, hO a ha, hO b hb,
        mergeOE_ind n (a / 2) (b / 2) (by omega) (by omega),
        mergeOE_ind n ((a + 1) / 2) ((b + 1) / 2) (by omega) (by omega),
        midEvens_cmp_interleave _ _ (by omega) (by omega) (by omega) (by omega)]
      funext j
      simp only [ind]
      apply decide_eq_decide.mpr
      omega

/-! ## The recursive sorters sort -/

/-- Every bit vector of length one is sorted. -/
theorem eq_ind_one (y : Fin 1 → Bool) : ∃ a ≤ 1, y = ind (1 - a) 1 :=
  eq_ind_of_monotone y fun i j _ => by
    rw [show i = j from Subsingleton.elim i j]

/-- **Batcher's bitonic sorter sorts every bit vector**, at every degree. -/
theorem sortB_ind : ∀ (n : Nat) (y : Fin (2 ^ n) → Bool),
    ∃ a ≤ 2 ^ n, sortB cmp n y = ind (2 ^ n - a) (2 ^ n)
  | 0, y => eq_ind_one y
  | n + 1, y => by
      obtain ⟨a, ha, hlo⟩ := sortB_ind n (lo y)
      obtain ⟨b, hb, hhi⟩ := sortB_ind n (hi y)
      refine ⟨a + b, by rw [Nat.pow_succ]; omega, ?_⟩
      change bfly cmp (n + 1) (append (sortB cmp n (lo y)) (rev (sortB cmp n (hi y)))) = _
      rw [hlo, hhi, rev_ind_final b hb, append_ind a b ha hb]
      have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      refine (bfly_ind (n + 1) (2 ^ n - a) (2 ^ n + b) (by omega) (by omega)).trans ?_
      congr 1; omega

/-- **Batcher's odd–even merge sorter sorts every bit vector**, at every degree. -/
theorem sortOE_ind : ∀ (n : Nat) (y : Fin (2 ^ n) → Bool),
    ∃ a ≤ 2 ^ n, sortOE cmp n y = ind (2 ^ n - a) (2 ^ n)
  | 0, y => eq_ind_one y
  | n + 1, y => by
      obtain ⟨a, ha, hlo⟩ := sortOE_ind n (lo y)
      obtain ⟨b, hb, hhi⟩ := sortOE_ind n (hi y)
      refine ⟨a + b, by rw [Nat.pow_succ]; omega, ?_⟩
      change mergeOE cmp (n + 1) (append (sortOE cmp n (lo y)) (sortOE cmp n (hi y))) = _
      rw [hlo, hhi, mergeOE_ind n a b ha hb]

/-- **Batcher's bitonic sorter sorts**, over every linear order and at every degree. -/
theorem sortB_sorts [LinearOrder α] (n : Nat) : Sorts (sortB cmp n : Net α (2 ^ n)) :=
  sorts_of (IsPerm.sortB cmp_swapCell n) fun x =>
    zero_one _ _ (fun _ hg => Commutes.sortB (Commutes.cmp hg) n) (fun y => by
      obtain ⟨a, _, h⟩ := sortB_ind n y; rw [h]; exact monotone_ind a) x

/-- **Batcher's odd–even merge sorter sorts**, over every linear order and at
every degree. -/
theorem sortOE_sorts [LinearOrder α] (n : Nat) : Sorts (sortOE cmp n : Net α (2 ^ n)) :=
  sorts_of (IsPerm.sortOE cmp_swapCell n) fun x =>
    zero_one _ _ (fun _ hg => Commutes.sortOE (Commutes.cmp hg) n) (fun y => by
      obtain ⟨a, _, h⟩ := sortOE_ind n y; rw [h]; exact monotone_ind a) x

end Ruby.Vec
