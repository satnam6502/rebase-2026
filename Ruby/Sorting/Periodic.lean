import Ruby.Sorting.Refinement

/-!
# The periodic sorters sort

A vector is `k`-sorted when every element is at most the element `k` places
later; then each residue class modulo `k` is sorted, and `1`-sorted is sorted.

Both of Batcher's mergers preserve `2 ^ j`-sortedness of their two halves
(`mergeB_ksorted`, `mergeOE_ksorted`): the recursive calls see
`2 ^ (j - 1)`-sorted halves, interleaving doubles the period back, and a
column of comparators between neighbouring residue classes keeps it. For
`j = 0` this is merging.

An `unriffle` splits a `2 ^ (j + 1)`-sorted vector into two `2 ^ j`-sorted
halves, so each pass of `unriffle ⨾ merge` halves the period. A vector of
`2 ^ n` elements is trivially `2 ^ n`-sorted, so `n` passes sort. By the
refinement laws `vfly_eq` and `qfly_eq` these are exactly the periodic sorters
`sortV` and `sortQ`.
-/

namespace Ruby.Vec

variable {α : Type}

/-- Every element is at most the element `k` places later. -/
def KSorted [Preorder α] {N : Nat} (k : Nat) (v : Fin N → α) : Prop :=
  ∀ i j : Fin N, j.val = i.val + k → v i ≤ v j

section Order

variable [Preorder α]

theorem KSorted.of_eq {N k : Nat} {u v : Fin N → α} (h : u = v) (hv : KSorted k v) :
    KSorted k u := h ▸ hv

theorem ksorted_of_monotone {N k : Nat} {v : Fin N → α} (hv : Monotone v) : KSorted k v :=
  fun i j h => hv (show i ≤ j from Fin.le_iff_val_le_val.mpr (by omega))

theorem ksorted_of_le {N k : Nat} (v : Fin N → α) (h : N ≤ k) : KSorted k v :=
  fun i j hij => absurd j.isLt (by omega)

theorem monotone_of_ksorted_one {N : Nat} {v : Fin N → α} (hv : KSorted 1 v) : Monotone v := by
  have step : ∀ t (i j : Fin N), j.val = i.val + t → v i ≤ v j := by
    intro t
    induction t with
    | zero => intro i j h; rw [show i = j from Fin.ext (by omega)]
    | succ t ih =>
      intro i j h
      have hi1 : i.val + 1 < N := by omega
      exact le_trans (hv i ⟨i.val + 1, hi1⟩ rfl) (ih ⟨i.val + 1, hi1⟩ j (by simp only; omega))
  intro i j hij
  have : i.val ≤ j.val := hij
  exact step (j.val - i.val) i j (by omega)

theorem evensIdx_ksorted {m k : Nat} {x : Fin (m * 2) → α} (hx : KSorted (2 * k) x) :
    KSorted k (evensIdx x) := fun i j h => hx _ _ (by simp only; omega)

theorem oddsIdx_ksorted {m k : Nat} {x : Fin (m * 2) → α} (hx : KSorted (2 * k) x) :
    KSorted k (oddsIdx x) := fun i j h => hx _ _ (by simp only; omega)

theorem interleave_ksorted {m k : Nat} {u v : Fin m → α} (hu : KSorted k u) (hv : KSorted k v) :
    KSorted (2 * k) (interleave u v) := by
  intro i j h
  simp only [interleave]
  split_ifs with h1 h2 h2
  · exact hu _ _ (by simp only; omega)
  · omega
  · omega
  · exact hv _ _ (by simp only; omega)

end Order

section Linear

variable [LinearOrder α]

/-- A column of comparators on the pairs `(2 i, 2 i + 1)` keeps an even period. -/
theorem evens_cmp_ksorted {m K : Nat} (hK : K % 2 = 0) {x : Fin (m * 2) → α} (hx : KSorted K x) :
    KSorted K (evens (m := m) cmp x) := by
  intro i j h
  simp only [evens_apply]
  have hp : j.val % 2 = i.val % 2 := by omega
  have h0 := hx ⟨2 * (i.val / 2), by omega⟩ ⟨2 * (j.val / 2), by omega⟩ (by simp only; omega)
  have h1 := hx ⟨2 * (i.val / 2) + 1, by omega⟩ ⟨2 * (j.val / 2) + 1, by omega⟩ (by simp only; omega)
  by_cases hi : i.val % 2 = 0
  · have ei : (⟨i.val % 2, by omega⟩ : Fin 2) = 0 := Fin.ext hi
    have ej : (⟨j.val % 2, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp only; omega)
    rw [ei, ej, cmp_zero, cmp_zero]
    exact min_le_min h0 h1
  · have ei : (⟨i.val % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
    have ej : (⟨j.val % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
    rw [ei, ej, cmp_one, cmp_one]
    exact max_le_max h0 h1

/-- The middle column of comparators, on the pairs `(2 i + 1, 2 i + 2)`, keeps an
even period of at least two. -/
theorem midEvens_cmp_ksorted {m K : Nat} (hK : K % 2 = 0) (hK2 : 2 ≤ K) {x : Fin (m * 2) → α}
    (hx : KSorted K x) : KSorted K (midEvens (m := m) cmp x) := by
  intro i j h
  have hj := j.isLt
  -- the wire at position `p` and its partner in the middle column
  have hstep : ∀ (p q : Nat) (hp : p < m * 2) (hq : q < m * 2), q = p + K →
      x ⟨p, hp⟩ ≤ x ⟨q, hq⟩ := fun p q hp hq hpq => hx _ _ hpq
  by_cases hiend : IsEnd i <;> by_cases hjend : IsEnd j <;>
    simp only [midEvens, hiend, hjend, ↓reduceIte] <;> unfold IsEnd at hiend hjend
  · -- both ends: `i = 0` and `j = 2 m - 1`, impossible for an even period
    omega
  · -- `i = 0`, `j` in the middle at an even position
    have hi0 : i.val = 0 := by omega
    have ej : (⟨(j.val - 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
    rw [ej, cmp_one, midPair_eq_of_not_end _ _ hjend]
    simp only [Fin.val_zero, Fin.val_one]
    refine le_trans ?_ (le_max_right _ _)
    exact hstep _ _ _ _ (by omega)
  · -- `i` in the middle at an odd position, `j = 2 m - 1`
    have hjl : j.val = m * 2 - 1 := by omega
    have ei : (⟨(i.val - 1) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp only; omega)
    rw [ei, cmp_zero, midPair_eq_of_not_end _ _ hiend]
    simp only [Fin.val_zero, Fin.val_one]
    refine le_trans (min_le_left _ _) ?_
    exact hstep _ _ _ _ (by omega)
  · -- both in the middle, at the same position in their pairs
    rw [midPair_eq_of_not_end _ _ hiend, midPair_eq_of_not_end _ _ hjend]
    have h0 := hstep (2 * ((i.val - 1) / 2) + 1) (2 * ((j.val - 1) / 2) + 1) (by omega) (by omega)
      (by omega)
    have h1 := hstep (2 * ((i.val - 1) / 2) + 1 + 1) (2 * ((j.val - 1) / 2) + 1 + 1) (by omega)
      (by omega) (by omega)
    by_cases hi : (i.val - 1) % 2 = 0
    · have ei : (⟨(i.val - 1) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext hi
      have ej : (⟨(j.val - 1) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext (by simp only; omega)
      rw [ei, ej, cmp_zero, cmp_zero]
      simp only [Fin.val_zero, Fin.val_one, Nat.add_zero]
      exact min_le_min h0 h1
    · have ei : (⟨(i.val - 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
      have ej : (⟨(j.val - 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by simp only; omega)
      rw [ei, ej, cmp_one, cmp_one]
      simp only [Fin.val_zero, Fin.val_one, Nat.add_zero]
      exact max_le_max h0 h1

end Linear

/-! ## The mergers keep the period of their halves -/

/-- The bitonic merger is a butterfly of half-size bitonic mergers. -/
theorem mergeB_split {k : Nat} (f : Net α 2) (B M : Net α (k * 2)) (hM : M = parl id rev ⨾ B)
    (x : Fin (k * 2 * 2) → α) :
    (parl id rev ⨾ (ilv B ⨾ evens f)) x =
      evens f (interleave (M (append (evensIdx (lo x)) (oddsIdx (hi x))))
        (M (append (oddsIdx (lo x)) (evensIdx (hi x))))) := by
  subst hM
  simp only [seq_apply, parl, lo_append, hi_append, id, ilv_apply, evensIdx_append,
    oddsIdx_append, evensIdx_rev, oddsIdx_rev]

/-- The odd–even merger is a butterfly of half-size odd–even mergers. -/
theorem mergeOE_split {k : Nat} (f : Net α 2) (M : Net α (k * 2)) (x : Fin (k * 2 * 2) → α) :
    (ilv M ⨾ midEvens f) x =
      midEvens f (interleave (M (append (evensIdx (lo x)) (evensIdx (hi x))))
        (M (append (oddsIdx (lo x)) (oddsIdx (hi x))))) := by
  conv_lhs => rw [← append_lo_hi x]
  simp only [seq_apply, ilv_apply, evensIdx_append, oddsIdx_append]

theorem pow_succ_even (j : Nat) : 2 ^ (j + 1) % 2 = 0 := by
  rw [Nat.pow_succ]; simp

theorem two_le_pow_succ (j : Nat) : 2 ≤ 2 ^ (j + 1) := by
  rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := j); omega

/-- **The bitonic merger keeps the period of its halves**, at every degree. -/
theorem mergeB_ksorted : ∀ (n j : Nat) (x : Fin (2 ^ (n + 1)) → Bool),
    KSorted (2 ^ j) (lo (m := 2 ^ n) x) → KSorted (2 ^ j) (hi (m := 2 ^ n) x) →
      KSorted (2 ^ j) (mergeB cmp n x)
  | 0, j, x, _, _ => by
      refine ksorted_of_monotone fun i i' hii' => ?_
      change cmp (parl (m := 1) id rev x) i ≤ cmp (parl (m := 1) id rev x) i'
      rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases i' with rfl | rfl
      · exact le_refl _
      · simp only [cmp_zero, cmp_one]; exact le_trans (min_le_left _ _) (le_max_left _ _)
      · exact absurd hii' (by decide)
      · exact le_refl _
  | n + 1, 0, x, hlo, hhi => by
      obtain ⟨a, ha, hla⟩ := eq_ind_of_monotone _ (monotone_of_ksorted_one hlo)
      obtain ⟨b, hb, hhb⟩ := eq_ind_of_monotone _ (monotone_of_ksorted_one hhi)
      have hx : x = append (ind (N := 2 ^ (n + 1)) (2 ^ (n + 1) - a) (2 ^ (n + 1)))
          (ind (2 ^ (n + 1) - b) (2 ^ (n + 1))) := by
        rw [← hla, ← hhb]; exact (append_lo_hi x).symm
      rw [hx, mergeB_ind (n + 1) a b ha hb]
      exact ksorted_of_monotone (monotone_ind _)
  | n + 1, j + 1, x, hlo, hhi => by
      have hsplit := mergeB_split (k := 2 ^ n) cmp (bfly cmp (n + 1)) (mergeB cmp n) rfl x
      refine KSorted.of_eq hsplit ?_
      have hj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
      rw [hj] at hlo hhi ⊢
      refine evens_cmp_ksorted (by omega) (interleave_ksorted ?_ ?_)
      · exact mergeB_ksorted n j _ (KSorted.of_eq (lo_append _ _) (evensIdx_ksorted hlo))
          (KSorted.of_eq (hi_append _ _) (oddsIdx_ksorted hhi))
      · exact mergeB_ksorted n j _ (KSorted.of_eq (lo_append _ _) (oddsIdx_ksorted hlo))
          (KSorted.of_eq (hi_append _ _) (evensIdx_ksorted hhi))

/-- **The odd–even merger keeps the period of its halves**, at every degree. -/
theorem mergeOE_ksorted : ∀ (n j : Nat) (x : Fin (2 ^ (n + 1)) → Bool),
    KSorted (2 ^ j) (lo (m := 2 ^ n) x) → KSorted (2 ^ j) (hi (m := 2 ^ n) x) →
      KSorted (2 ^ j) (mergeOE cmp (n + 1) x)
  | 0, j, x, _, _ => by
      refine ksorted_of_monotone fun i i' hii' => ?_
      change cmp x i ≤ cmp x i'
      rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases i' with rfl | rfl
      · exact le_refl _
      · simp only [cmp_zero, cmp_one]; exact le_trans (min_le_left _ _) (le_max_left _ _)
      · exact absurd hii' (by decide)
      · exact le_refl _
  | n + 1, 0, x, hlo, hhi => by
      obtain ⟨a, ha, hla⟩ := eq_ind_of_monotone _ (monotone_of_ksorted_one hlo)
      obtain ⟨b, hb, hhb⟩ := eq_ind_of_monotone _ (monotone_of_ksorted_one hhi)
      have hx : x = append (ind (N := 2 ^ (n + 1)) (2 ^ (n + 1) - a) (2 ^ (n + 1)))
          (ind (2 ^ (n + 1) - b) (2 ^ (n + 1))) := by
        rw [← hla, ← hhb]; exact (append_lo_hi x).symm
      rw [hx, mergeOE_ind (n + 1) a b ha hb]
      exact ksorted_of_monotone (monotone_ind _)
  | n + 1, j + 1, x, hlo, hhi => by
      have hsplit := mergeOE_split (k := 2 ^ n) cmp (mergeOE cmp (n + 1)) x
      refine KSorted.of_eq hsplit ?_
      have hj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
      rw [hj] at hlo hhi ⊢
      refine midEvens_cmp_ksorted (by omega) (by have := Nat.one_le_two_pow (n := j); omega)
        (interleave_ksorted ?_ ?_)
      · exact mergeOE_ksorted n j _ (KSorted.of_eq (lo_append _ _) (evensIdx_ksorted hlo))
          (KSorted.of_eq (hi_append _ _) (evensIdx_ksorted hhi))
      · exact mergeOE_ksorted n j _ (KSorted.of_eq (lo_append _ _) (oddsIdx_ksorted hlo))
          (KSorted.of_eq (hi_append _ _) (oddsIdx_ksorted hhi))

/-! ## Passes of `unriffle ⨾ merge` sort -/

/-- If one pass halves the period, `k` passes divide it by `2 ^ k`. -/
theorem hrep_ksorted {N : Nat} (P : Net Bool N)
    (hP : ∀ j x, KSorted (2 ^ (j + 1)) x → KSorted (2 ^ j) (P x)) :
    ∀ k j x, KSorted (2 ^ (j + k)) x → KSorted (2 ^ j) (hrep k P x)
  | 0, j, x, hx => hx
  | k + 1, j, x, hx => by
      change KSorted (2 ^ j) (hrep k P (P x))
      exact hrep_ksorted P hP k j (P x) (hP (j + k) x (by rw [show j + k + 1 = j + (k + 1) by omega]; exact hx))

theorem unriffle_mergeB_pass (n : Nat) :
    ∀ j (x : Fin (2 ^ (n + 1)) → Bool), KSorted (2 ^ (j + 1)) x →
      KSorted (2 ^ j) ((unriffle (m := 2 ^ n) ⨾ mergeB cmp n) x) := by
  intro j x hx
  have hj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
  rw [hj] at hx
  exact mergeB_ksorted n j _ (by simpa [unriffle] using evensIdx_ksorted (m := 2 ^ n) hx)
    (by simpa [unriffle] using oddsIdx_ksorted (m := 2 ^ n) hx)

theorem unriffle_mergeOE_pass (n : Nat) :
    ∀ j (x : Fin (2 ^ (n + 1)) → Bool), KSorted (2 ^ (j + 1)) x →
      KSorted (2 ^ j) ((unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) x) := by
  intro j x hx
  have hj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
  rw [hj] at hx
  exact mergeOE_ksorted n j _ (by simpa [unriffle] using evensIdx_ksorted (m := 2 ^ n) hx)
    (by simpa [unriffle] using oddsIdx_ksorted (m := 2 ^ n) hx)

/-! ## The periodic law

`n + 1` passes of `unriffle ⨾ merge` sort `2 ^ (n + 1)` wires, for either of
Batcher's mergers. This is a law about the composition itself; the periodic
sorters `sortV` and `sortQ` meet it through the wiring laws `vfly_eq` and
`qfly_eq`. -/

/-- On bits: `n + 1` passes of `unriffle ⨾ mergeB` sort. -/
theorem periodicB_monotone_bool (n : Nat) (y : Fin (2 ^ (n + 1)) → Bool) :
    Monotone (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeB cmp n) y) :=
  monotone_of_ksorted_one
    (hrep_ksorted _ (unriffle_mergeB_pass n) (n + 1) 0 y (ksorted_of_le y (by simp)))

/-- On bits: `n + 1` passes of `unriffle ⨾ mergeOE` sort. -/
theorem periodicOE_monotone_bool (n : Nat) (y : Fin (2 ^ (n + 1)) → Bool) :
    Monotone (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) y) :=
  monotone_of_ksorted_one
    (hrep_ksorted _ (unriffle_mergeOE_pass n) (n + 1) 0 y (ksorted_of_le y (by simp)))

/-- **The periodic law for the bitonic merger**: `n + 1` passes of
`unriffle ⨾ mergeB` sort, over every linear order. -/
theorem periodicB_sorts [LinearOrder α] (n : Nat) :
    Sorts (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeB cmp n) : Net α (2 ^ (n + 1))) :=
  sorts_of ((IsPerm.unriffle.seq (IsPerm.mergeB cmp_swapCell n)).hrep (n + 1)) fun x =>
    zero_one _ _ (fun _ hg => (Commutes.unriffle.seq ((Commutes.cmp hg).mergeB n)).hrep (n + 1))
      (periodicB_monotone_bool n) x

/-- **The periodic law for the odd–even merger**: `n + 1` passes of
`unriffle ⨾ mergeOE` sort, over every linear order. -/
theorem periodicOE_sorts [LinearOrder α] (n : Nat) :
    Sorts (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) : Net α (2 ^ (n + 1))) :=
  sorts_of ((IsPerm.unriffle.seq (IsPerm.mergeOE cmp_swapCell (n + 1))).hrep (n + 1)) fun x =>
    zero_one _ _
      (fun _ hg => (Commutes.unriffle.seq ((Commutes.cmp hg).mergeOE (n + 1))).hrep (n + 1))
      (periodicOE_monotone_bool n) x

/-- A network on one wire sorts. -/
theorem sorts_one [LinearOrder α] (F : Net α (2 ^ 0)) (hF : F = id) : Sorts F := fun x => by
  rw [hF]; simp

/-- **The periodic balanced sorter sorts**, over every linear order and at every
degree: the periodic law, through `vfly_eq`. -/
theorem sortV_sorts [LinearOrder α] : ∀ n, Sorts (sortV cmp n : Net α (2 ^ n))
  | 0 => sorts_one _ rfl
  | n + 1 => by rw [sortV_eq cmp_symm]; exact periodicB_sorts n

/-- **The periodic Canfield–Williamson sorter sorts**, over every linear order
and at every degree: the periodic law, through `qfly_eq`. -/
theorem sortQ_sorts [LinearOrder α] : ∀ n, Sorts (sortQ cmp n : Net α (2 ^ n))
  | 0 => sorts_one _ rfl
  | n + 1 => by rw [sortQ_eq cmp_symm]; exact periodicOE_sorts n

end Ruby.Vec
