import Ruby.Sorting.Merge

/-!
# Laws of the connection patterns

The algebra used to calculate with the sorter networks. Each law is an
equation between functions on vectors, proved once from index arithmetic; the
calculations in `Ruby.Sorting.Refinement` then only rewrite with laws.

Every vector of length `4 m` is four interleaved quarters, `quad P Q R S`
(`eq_quad`), so laws about the double riffles reduce to laws about `quad`.
-/

namespace Ruby.Vec

variable {α : Type}

/-! ## Interleaving, appending and reversing -/

theorem interleave_append {k : Nat} (a b c d : Fin k → α) :
    interleave (m := k * 2) (append a b) (append c d) = append (interleave a c) (interleave b d) := by
  funext j; simp only [interleave, append]
  split_ifs <;> idx_eq

theorem rev_interleave {k : Nat} (a b : Fin k → α) :
    rev (interleave a b) = interleave (rev b) (rev a) := by
  funext j; simp only [rev, interleave]
  split_ifs <;> idx_eq

theorem rev_append {k : Nat} (a b : Fin k → α) : rev (append a b) = append (rev b) (rev a) := by
  funext j; simp only [rev, append]
  split_ifs <;> idx_eq

theorem rev_rev {n : Nat} (x : Fin n → α) : rev (rev x) = x := by
  funext j; simp only [rev]; congr 1; apply Fin.ext; simp only; omega

theorem evensIdx_rev {k : Nat} (x : Fin (k * 2) → α) : evensIdx (rev x) = rev (oddsIdx x) := by
  funext i; simp only [evensIdx, oddsIdx, rev]; congr 1; apply Fin.ext; simp only; omega

theorem oddsIdx_rev {k : Nat} (x : Fin (k * 2) → α) : oddsIdx (rev x) = rev (evensIdx x) := by
  funext i; simp only [evensIdx, oddsIdx, rev]; congr 1; apply Fin.ext; simp only; omega

/-! ## Quarters -/

/-- Four equal-length vectors, interleaved: `[p₀, q₀, r₀, s₀, p₁, q₁, r₁, s₁, …]`. -/
def quad {k : Nat} (P Q R S : Fin k → α) : Fin (k * 2 * 2) → α :=
  interleave (interleave P R) (interleave Q S)

/-- Every vector of length `4 k` is four interleaved quarters. -/
theorem eq_quad {k : Nat} (x : Fin (k * 2 * 2) → α) :
    x = quad (evensIdx (evensIdx x)) (evensIdx (oddsIdx x)) (oddsIdx (evensIdx x))
      (oddsIdx (oddsIdx x)) := by
  simp only [quad, interleave_evensIdx_oddsIdx]

theorem quad_apply {k : Nat} (P Q R S : Fin k → α) (j : Fin (k * 2 * 2)) :
    quad P Q R S j =
      if j.val % 4 = 0 then P ⟨j / 4, by omega⟩ else if j.val % 4 = 1 then Q ⟨j / 4, by omega⟩
      else if j.val % 4 = 2 then R ⟨j / 4, by omega⟩ else S ⟨j / 4, by omega⟩ := by
  simp only [quad, interleave]
  split_ifs <;> idx_eq

theorem unriffle_quad {k : Nat} (P Q R S : Fin k → α) :
    unriffle (quad P Q R S) = append (interleave P R) (interleave Q S) := by
  simp [quad]

theorem evensIdx_quad {k : Nat} (P Q R S : Fin k → α) :
    evensIdx (quad P Q R S) = interleave P R := by simp [quad]

theorem oddsIdx_quad {k : Nat} (P Q R S : Fin k → α) :
    oddsIdx (quad P Q R S) = interleave Q S := by simp [quad]

/-- `alt` swaps the third and fourth quarters. -/
theorem alt_quad {k : Nat} (P Q R S : Fin k → α) : alt (quad P Q R S) = quad P Q S R := by
  funext j
  simp only [alt, quad_apply]
  have hv := altIdx_val j
  have hlt := j.isLt
  split_ifs at hv ⊢ <;> idx_eq

/-! ## Functor laws -/

theorem two_seq {m : Nat} (F G : Net α m) : two (F ⨾ G) = two F ⨾ two G := by
  funext x; simp [two, parl]

theorem ilv_seq {m : Nat} (F G : Net α m) : ilv (F ⨾ G) = ilv F ⨾ ilv G := by
  funext x; simp [ilv_apply]

theorem ilv_id {m : Nat} : ilv (id : Net α m) = id := by
  funext x; simp [ilv_apply]

theorem two_id {m : Nat} : two (id : Net α m) = id := by
  funext x; simp [two, parl]

/-- `ilv riffle` undoes `ilv unriffle`. -/
theorem ilv_riffle_unriffle {m : Nat} : (ilv riffle ⨾ ilv unriffle : Net α (m * 2 * 2)) = id := by
  rw [← ilv_seq]
  have : (riffle ⨾ unriffle : Net α (m * 2)) = id := by funext x; simp
  rw [this, ilv_id]

theorem que_seq {m : Nat} (F G : Net α (m * 2)) : que (F ⨾ G) = que F ⨾ que G := by
  funext x
  simp only [que, two_seq, seq_apply]
  have := congrFun (ilv_riffle_unriffle (α := α) (m := m)) (two F (ilv unriffle x))
  simp only [seq_apply, id] at this
  rw [this]

/-! ## Laws of the double riffles -/

/-- **W3.** Unriffling inside `ilv`, then in both halves, is unriffling twice. -/
theorem two_unriffle_ilv_unriffle {k : Nat} (x : Fin (k * 2 * 2) → α) :
    two unriffle (ilv unriffle x) = unriffle (unriffle x) := by
  rw [eq_quad x]
  generalize evensIdx (evensIdx x) = P
  generalize evensIdx (oddsIdx x) = Q
  generalize oddsIdx (evensIdx x) = R
  generalize oddsIdx (oddsIdx x) = S
  rw [ilv_apply, evensIdx_quad, oddsIdx_quad, unriffle_interleave, unriffle_interleave,
    interleave_append, two_append, unriffle_interleave, unriffle_interleave, unriffle_quad]
  simp only [unriffle, evensIdx_append, oddsIdx_append, evensIdx_interleave, oddsIdx_interleave]

/-- The odd positions, reversed. -/
def oddsRev {m : Nat} : Net α (m * 2) := unriffle ⨾ parl id rev ⨾ riffle

/-- **W5.** The wiring at the heart of the balanced merger. -/
theorem ilv_parl_rev_ilv_unriffle_alt {k : Nat} (x : Fin (k * 2 * 2) → α) :
    ilv (parl id rev) (ilv unriffle (alt x)) = oddsRev (parl id rev (unriffle x)) := by
  rw [eq_quad x]
  generalize evensIdx (evensIdx x) = P
  generalize evensIdx (oddsIdx x) = Q
  generalize oddsIdx (evensIdx x) = R
  generalize oddsIdx (oddsIdx x) = S
  have e₁ : ilv unriffle (quad P Q S R) = append (interleave P Q) (interleave S R) := by
    rw [ilv_apply, evensIdx_quad, oddsIdx_quad, unriffle_interleave, unriffle_interleave,
      interleave_append]
  rw [alt_quad, e₁, ilv_apply, evensIdx_append, oddsIdx_append, evensIdx_interleave,
    evensIdx_interleave, oddsIdx_interleave, oddsIdx_interleave, parl_append, parl_append,
    unriffle_quad, parl_append]
  simp only [oddsRev, seq_apply, id, rev_interleave, unriffle, evensIdx_append, oddsIdx_append,
    evensIdx_interleave, oddsIdx_interleave, parl_append, rev_append, rev_rev, riffle_append,
    interleave_append]

/-! ## Symmetric cells ignore swaps inside their pairs -/

section Symm

variable {f : Net α 2}

theorem evens_interleave_comm (hf : Symm f) {k : Nat} (u v : Fin k → α) :
    evens f (interleave v u) = evens f (interleave u v) := by
  funext j
  rw [evens_interleave_apply, evens_interleave_apply, ← hf]
  congr 1; funext b
  have := b.isLt
  simp only [rev]
  split_ifs <;> idx_eq

/-- `alt` swaps pairs that `evens` then treats symmetrically. -/
theorem evens_alt (hf : Symm f) {m : Nat} (x : Fin (m * 2) → α) : evens f (alt x) = evens f x := by
  funext j
  simp only [evens_apply, alt]
  by_cases h : (j.val / 2) % 2 = 1
  · rw [← hf]
    congr 1; funext b
    have := b.isLt
    simp only [rev]
    congr 1; apply Fin.ext
    have hv := altIdx_val (⟨2 * (j / 2) + (2 - 1 - b.val), by omega⟩ : Fin (m * 2))
    simp only at hv ⊢
    split_ifs at hv <;> omega
  · congr 1; funext b
    have := b.isLt
    congr 1; apply Fin.ext
    have hv := altIdx_val (⟨2 * (j / 2) + b.val, by omega⟩ : Fin (m * 2))
    simp only at hv ⊢
    split_ifs at hv <;> omega

/-- The middle column treats the swapped second and third quarters symmetrically. -/
theorem midEvens_quad_swap (hf : Symm f) {k : Nat} (P Q R S : Fin k → α) :
    midEvens f (quad P Q R S) = midEvens f (quad P R Q S) := by
  funext j
  have hlt := j.isLt
  by_cases hend : IsEnd j
  · simp only [midEvens, hend, ↓reduceIte, quad_apply]
    unfold IsEnd at hend
    split_ifs <;> first | omega | rfl
  · have hend' := hend
    unfold IsEnd at hend'
    simp only [midEvens, hend, ↓reduceIte]
    by_cases hi : ((j.val - 1) / 2) % 2 = 0
    · rw [← hf (midPair _ j)]
      congr 1; funext b
      have := b.isLt
      simp only [rev, midPair_of_not_end _ _ hend', quad_apply]
      split_ifs <;> idx_eq
    · congr 1; funext b
      have := b.isLt
      simp only [midPair_of_not_end _ _ hend', quad_apply]
      split_ifs <;> idx_eq

/-- **W4.** Behind a symmetric middle column, `ilv riffle` is `riffle`. -/
theorem midEvens_ilv_riffle (hf : Symm f) {k : Nat} (x : Fin (k * 2 * 2) → α) :
    midEvens f (ilv riffle x) = midEvens f (riffle x) := by
  rw [← append_lo_hi x, ← interleave_evensIdx_oddsIdx (lo x),
    ← interleave_evensIdx_oddsIdx (hi x)]
  generalize evensIdx (lo x) = A
  generalize oddsIdx (lo x) = B
  generalize evensIdx (hi x) = C
  generalize oddsIdx (hi x) = D
  rw [ilv_apply, evensIdx_append, oddsIdx_append, evensIdx_interleave, evensIdx_interleave,
    oddsIdx_interleave, oddsIdx_interleave, riffle_append, riffle_append, riffle_append]
  exact midEvens_quad_swap hf A B C D

/-- A butterfly of symmetric cells does not see its input reversed. -/
theorem bfly_rev (hf : Symm f) : ∀ (n : Nat) (x : Fin (2 ^ n) → α), bfly f n (rev x) = bfly f n x
  | 0, x => by
      funext i; simp only [bfly, id, rev]; congr 1; apply Fin.ext; have := i.isLt
      simp only [Nat.pow_zero] at this ⊢; omega
  | 1, x => hf x
  | n + 2, x => by
      have key : ∀ y : Fin (2 ^ (n + 1) * 2) → α,
          evens (m := 2 ^ (n + 1)) f (ilv (bfly f (n + 1)) (rev y)) =
            evens (m := 2 ^ (n + 1)) f (ilv (bfly f (n + 1)) y) := by
        intro y
        rw [ilv_apply, ilv_apply, evensIdx_rev, oddsIdx_rev, bfly_rev hf (n + 1),
          bfly_rev hf (n + 1), evens_interleave_comm hf]
      exact key x

end Symm

end Ruby.Vec
