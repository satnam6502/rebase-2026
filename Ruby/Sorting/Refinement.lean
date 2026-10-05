import Ruby.Sorting.Laws

/-!
# The four sorter cores, related by calculation

Bird–Meertens style refinement steps between the four sorters of
Claessen, Sheeran and Singh. Each step is an equation between networks that
holds for *any* symmetric two-input cell, so it is a fact about wiring, not
about comparison:

* all four mergers are one schema, `fly P L`: a connection pattern `P` around
  the merger of half the size, then a last column `L` (`bfly_eq_fly`, …);
* `sortB` has the same shape as `sortOE` once its merger is read as a merger of
  two sorted halves, `mergeB` (`sortB_succ`, `sortOE_succ`);
* the periodic mergers are the recursive mergers behind an `unriffle`:
  `vfly n = unriffle ⨾ mergeB` (`vfly_eq`) and `qfly n = unriffle ⨾ mergeOE`
  (`qfly_eq`).

So the periodic sorters `sortV` and `sortQ` are `n` passes of
`unriffle ⨾ merge`, where `merge` is Batcher's bitonic or odd–even merger.
-/

namespace Ruby.Vec

variable {α : Type}

/-! ## One schema for the four mergers -/

/-- A butterfly-shaped merger: a connection pattern `P` around the merger of
half the size, then a last column `L`. -/
def fly (P : ∀ n, Net α (2 ^ (n + 1)) → Net α (2 ^ (n + 2)))
    (L : ∀ n, Net α 2 → Net α (2 ^ (n + 2))) (f : Net α 2) : (n : Nat) → Net α (2 ^ n)
  | 0 => id
  | 1 => f
  | n + 2 => P n (fly P L f (n + 1)) ⨾ L n f

theorem bfly_eq_fly (f : Net α 2) :
    ∀ n, bfly f n = fly (fun _ => ilv) (fun _ => evens) f n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (fun g => ilv g ⨾ evens f) (bfly_eq_fly f (n + 1))

theorem mergeOE_eq_fly (f : Net α 2) :
    ∀ n, mergeOE f n = fly (fun _ => ilv) (fun _ => midEvens) f n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (fun g => ilv g ⨾ midEvens f) (mergeOE_eq_fly f (n + 1))

theorem vfly_eq_fly (f : Net α 2) :
    ∀ n, vfly f n = fly (fun _ => vee) (fun _ => evens) f n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (fun g => vee g ⨾ evens f) (vfly_eq_fly f (n + 1))

theorem qfly_eq_fly (f : Net α 2) :
    ∀ n, qfly f n = fly (fun n => que (m := 2 ^ n)) (fun _ => midEvens) f n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (fun g => que (m := 2 ^ n) g ⨾ midEvens f) (qfly_eq_fly f (n + 1))

/-! ## The bitonic sorter has the odd–even sorter's shape -/

/-- **`sortB` sorts both halves and then merges.** Reversing the second sorted
half is part of the bitonic merger `mergeB`. -/
theorem sortB_succ (f : Net α 2) (n : Nat) : sortB f (n + 1) = two (sortB f n) ⨾ mergeB f n := by
  funext x
  change bfly f (n + 1) (append (sortB f n (lo x)) (rev (sortB f n (hi x)))) =
    bfly f (n + 1) (parl (m := 2 ^ n) id rev (append (sortB f n (lo x)) (sortB f n (hi x))))
  rw [parl_append]; rfl

theorem sortOE_succ (f : Net α 2) (n : Nat) :
    sortOE f (n + 1) = two (sortOE f n) ⨾ mergeOE f (n + 1) := rfl

/-! ## The periodic mergers are the recursive ones behind an `unriffle` -/

theorem unriffle_two (x : Fin (1 * 2) → α) : unriffle x = x := by
  funext j; simp only [unriffle, append, evensIdx, oddsIdx]
  split_ifs <;> idx_eq

theorem parl_id_rev_two (x : Fin (1 * 2) → α) : parl id rev x = x := by
  funext j; simp only [parl, append, lo, hi, rev, id]
  split_ifs <;> idx_eq

/-- A reversal of the odd positions is invisible to an `ilv` of a network that
ignores reversals. -/
theorem ilv_oddsRev {m : Nat} {B : Net α m} (hB : ∀ z, B (rev z) = B z) (y : Fin (m * 2) → α) :
    ilv B (oddsRev y) = ilv B y := by
  simp only [oddsRev, seq_apply, ilv_apply, riffle, evensIdx_interleave, oddsIdx_interleave,
    unriffle, parl_append, lo_append, hi_append, id, hB]

/-- The inductive step of `vfly_eq`, at a generic size: a calculation in which
every line is a network and every step names its law. -/
theorem vee_step {k : Nat} {f : Net α 2} (hf : Symm f) (V B : Net α (k * 2))
    (hV : V = unriffle ⨾ parl id rev ⨾ B) (hB : ∀ z, B (rev z) = B z)
    (x : Fin (k * 2 * 2) → α) :
    evens f (alt (ilv V (alt x))) = evens f (ilv B (parl id rev (unriffle x))) :=
  calc evens f (alt (ilv V (alt x)))
      = evens f (ilv V (alt x)) := by                                    -- f is symmetric
          rw [evens_alt hf]
    _ = evens f (ilv (unriffle ⨾ parl id rev ⨾ B) (alt x)) := by         -- induction
          rw [hV]
    _ = evens f (ilv B (ilv (parl id rev) (ilv unriffle (alt x)))) := by  -- ilv is a functor
          rw [ilv_seq, ilv_seq]; rfl
    _ = evens f (ilv B (oddsRev (parl id rev (unriffle x)))) := by       -- W5
          rw [ilv_parl_rev_ilv_unriffle_alt]
    _ = evens f (ilv B (parl id rev (unriffle x))) := by                 -- a butterfly ignores
          rw [ilv_oddsRev hB]                                            -- a reversal

/-- **Dowd et al.'s balanced merger is Batcher's bitonic merger after an
`unriffle`**, for any symmetric cell. -/
theorem vfly_eq {f : Net α 2} (hf : Symm f) : ∀ n, vfly f (n + 1) = unriffle ⨾ mergeB f n
  | 0 => by
      funext x
      change f x = f (parl (m := 1) id rev (unriffle (m := 1) x))
      rw [unriffle_two, parl_id_rev_two]
  | n + 1 => by
      funext x
      exact vee_step (k := 2 ^ n) hf (vfly f (n + 1)) (bfly f (n + 1)) (vfly_eq hf n)
        (bfly_rev hf (n + 1)) x

/-- The inductive step of `qfly_eq`, at a generic size: a calculation in which
every line is a network and every step names its law. -/
theorem que_step {k : Nat} {f : Net α 2} (hf : Symm f) (Q M : Net α (k * 2))
    (hQ : Q = unriffle ⨾ M) (x : Fin (k * 2 * 2) → α) :
    midEvens f (que Q x) = midEvens f (ilv M (unriffle x)) :=
  have hcancel : ∀ z : Fin (k * 2 * 2) → α, ilv unriffle (ilv riffle z) = z :=
    fun z => congrFun (ilv_riffle_unriffle (α := α) (m := k)) z
  calc midEvens f (que Q x)
      = midEvens f (que (unriffle ⨾ M) x) := by                          -- induction
          rw [hQ]
    _ = midEvens f (que M (que unriffle x)) := by                         -- que is a functor
          rw [que_seq]; rfl
    _ = midEvens f (ilv riffle (two M (two unriffle (ilv unriffle x)))) := by
          simp only [que, seq_apply, hcancel]                             -- ilv riffle undoes
                                                                          -- ilv unriffle
    _ = midEvens f (ilv riffle (two M (unriffle (unriffle x)))) := by     -- W3
          rw [two_unriffle_ilv_unriffle]
    _ = midEvens f (riffle (two M (unriffle (unriffle x)))) := by         -- W4, and f is
          rw [midEvens_ilv_riffle hf]                                     -- symmetric
    _ = midEvens f (ilv M (unriffle x)) := rfl                            -- definition of ilv

/-- **Canfield and Williamson's merger is Batcher's odd–even merger after an
`unriffle`**, for any symmetric cell. -/
theorem qfly_eq {f : Net α 2} (hf : Symm f) : ∀ n, qfly f (n + 1) = unriffle ⨾ mergeOE f (n + 1)
  | 0 => by
      funext x
      change f x = f (unriffle (m := 1) x)
      rw [unriffle_two]
  | n + 1 => by
      funext x
      exact que_step (k := 2 ^ n) hf (qfly f (n + 1)) (mergeOE f (n + 1)) (qfly_eq hf n) x

/-- The periodic sorter `sortV` is `n` bitonic mergers, each behind an `unriffle`. -/
theorem sortV_eq {f : Net α 2} (hf : Symm f) (n : Nat) :
    sortV f (n + 1) = hrep (n + 1) (unriffle ⨾ mergeB f n) := by
  rw [sortV, vfly_eq hf]; rfl

/-- The periodic sorter `sortQ` is `n` odd–even mergers, each behind an `unriffle`. -/
theorem sortQ_eq {f : Net α 2} (hf : Symm f) (n : Nat) :
    sortQ f (n + 1) = hrep (n + 1) (unriffle ⨾ mergeOE f (n + 1)) := by
  rw [sortQ, qfly_eq hf]; rfl

end Ruby.Vec
