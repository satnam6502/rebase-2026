import Ruby.Sorting.Periodic

/-!
# From each sorter core to the next, by calculation

A Bird–Meertens derivation through the four sorter cores:

```
sortB  ──(1) merger exchange on sorted halves──▶  sortOE
sortOE ──(2) the periodic law, then qfly_eq────▶  sortQ
sortQ  ──(3) merger exchange in periodic passes─▶  sortV
```

Each step is a `calc` in which every line is a network and every step names
its law. Two kinds of law are used:

* **wiring laws**, which hold for *any* symmetric two-input cell and are proved
  by index calculation (`sortB_succ`, `qfly_eq`, `vfly_eq`, built from W3, W4,
  W5 and "a butterfly ignores a reversal" in `Ruby.Sorting.Laws`);
* **merging laws**, which hold for the comparator: the two mergers agree on
  inputs whose halves are sorted (`merge_exchange`), and `n + 1` passes of
  `unriffle ⨾ merge` sort for either merger (`periodicB_sorts`,
  `periodicOE_sorts`).

The paper's own lemma `que (ilv f) = ilv (ilv f)` (`que_ilv`) falls out of the
same wiring laws, and its counterexample shows that the `unriffle` in front of
each periodic pass is needed (`bfly_hrep_counterexample`).
-/

namespace Ruby.Vec

variable {α : Type}

/-! ## The merging laws -/

/-- Both halves of a vector are sorted. -/
def HalvesSorted [Preorder α] {m : Nat} (x : Fin (m * 2) → α) : Prop :=
  Monotone (lo x) ∧ Monotone (hi x)

/-- The zero–one principle, for inputs whose halves are sorted. -/
theorem zero_one_halves [LinearOrder α] {m : Nat} (F : Net α (m * 2)) (F₂ : Net Bool (m * 2))
    (hcomm : ∀ g : α → Bool, Monotone g → Commutes g F F₂)
    (hsort : ∀ y, HalvesSorted y → Monotone (F₂ y)) (x : Fin (m * 2) → α)
    (hx : HalvesSorted x) : Monotone (F x) := by
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
  have hm := hsort (g ∘ x) ⟨hg.comp hx.1, hg.comp hx.2⟩ hij
  rw [← hcomm g hg x] at hm
  have h1 : g (F x i) = true := by simp [g]
  have h2 : g (F x j) = false := by simp [g, not_le.mpr hlt]
  simp only [Function.comp_apply, h1, h2] at hm
  exact absurd hm (by decide)

theorem halves_eq_append {m : Nat} {y : Fin (m * 2) → Bool} (hy : HalvesSorted y) :
    ∃ a ≤ m, ∃ b ≤ m, y = append (ind (N := m) (m - a) m) (ind (m - b) m) := by
  obtain ⟨a, ha, hla⟩ := eq_ind_of_monotone _ hy.1
  obtain ⟨b, hb, hhb⟩ := eq_ind_of_monotone _ hy.2
  exact ⟨a, ha, b, hb, by rw [← hla, ← hhb, append_lo_hi]⟩

/-- **The bitonic merger merges**: given sorted halves, its output is sorted. -/
theorem mergeB_monotone [LinearOrder α] (n : Nat) (x : Fin (2 ^ (n + 1)) → α)
    (hx : HalvesSorted (m := 2 ^ n) x) : Monotone (mergeB cmp n x) :=
  zero_one_halves (m := 2 ^ n) (mergeB cmp n) (mergeB cmp n)
    (fun _ hg => (Commutes.cmp hg).mergeB n)
    (fun y hy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := halves_eq_append hy
      rw [mergeB_ind n a b ha hb]; exact monotone_ind _) x hx

/-- **The odd–even merger merges**: given sorted halves, its output is sorted. -/
theorem mergeOE_monotone [LinearOrder α] (n : Nat) (x : Fin (2 ^ (n + 1)) → α)
    (hx : HalvesSorted (m := 2 ^ n) x) : Monotone (mergeOE cmp (n + 1) x) :=
  zero_one_halves (m := 2 ^ n) (mergeOE cmp (n + 1)) (mergeOE cmp (n + 1))
    (fun _ hg => (Commutes.cmp hg).mergeOE (n + 1))
    (fun y hy => by
      obtain ⟨a, ha, b, hb, rfl⟩ := halves_eq_append hy
      rw [mergeOE_ind n a b ha hb]; exact monotone_ind _) x hx

/-- Two networks that both permute and both produce sorted output agree. -/
theorem eq_of_perm_monotone [LinearOrder α] {n : Nat} {F G : Net α n} {x : Fin n → α}
    (hF : (List.ofFn (F x)).Perm (List.ofFn x)) (hG : (List.ofFn (G x)).Perm (List.ofFn x))
    (hFm : Monotone (F x)) (hGm : Monotone (G x)) : F x = G x :=
  List.ofFn_injective (List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hFm)
    (List.sortedLE_ofFn_iff.mpr hGm) (hF.trans hG.symm))

/-- **Merger exchange.** On inputs whose halves are sorted, Batcher's bitonic and
odd–even mergers compute the same thing: the merge. -/
theorem merge_exchange [LinearOrder α] (n : Nat) (x : Fin (2 ^ (n + 1)) → α)
    (hx : HalvesSorted (m := 2 ^ n) x) : mergeB cmp n x = mergeOE cmp (n + 1) x :=
  eq_of_perm_monotone (IsPerm.mergeB cmp_swapCell n x) (IsPerm.mergeOE cmp_swapCell (n + 1) x)
    (mergeB_monotone n x hx) (mergeOE_monotone n x hx)

/-- Two sorters compute the same function: `mergeSort`. -/
theorem eq_of_sorts [LinearOrder α] {n : Nat} {F G : Net α n} (hF : Sorts F) (hG : Sorts G) :
    F = G := by
  funext x; exact List.ofFn_injective ((hF x).trans (hG x).symm)

theorem Sorts.monotone [LinearOrder α] {n : Nat} {F : Net α n} (hF : Sorts F) (x : Fin n → α) :
    Monotone (F x) :=
  List.sortedLE_ofFn_iff.mp (hF x ▸ List.sortedLE_mergeSort)

/-- Two sorters of halves deliver sorted halves. -/
theorem two_halvesSorted [LinearOrder α] {m : Nat} {F : Net α m} (hF : Sorts F)
    (x : Fin (m * 2) → α) : HalvesSorted (two F x) := by
  refine ⟨?_, ?_⟩
  · change Monotone (lo (append (F (lo x)) (F (hi x))))
    rw [lo_append]; exact hF.monotone _
  · change Monotone (hi (append (F (lo x)) (F (hi x))))
    rw [hi_append]; exact hF.monotone _

/-! ## Step 1: the bitonic sorter refines to the odd–even sorter -/

/-- **From `sortB` to `sortOE`.** Both sort the halves and then merge; the
reversal of the bitonic sorter belongs to its merger, and the two mergers
agree on sorted halves. -/
theorem sortB_eq_sortOE [LinearOrder α] : ∀ n, (sortB cmp n : Net α (2 ^ n)) = sortOE cmp n
  | 0 => rfl
  | n + 1 =>
    calc (sortB cmp (n + 1) : Net α (2 ^ (n + 1)))
        = (two (sortB cmp n) ⨾ mergeB cmp n : Net α (2 ^ (n + 1))) := by  -- the reversal belongs
            exact sortB_succ cmp n                                 -- to the merger
      _ = (two (sortB cmp n) ⨾ mergeOE cmp (n + 1) : Net α (2 ^ (n + 1))) := by  -- merger exchange on
            funext x                                               -- sorted halves
            exact merge_exchange n _ (two_halvesSorted (sortB_sorts n) x)
      _ = (two (sortOE cmp n) ⨾ mergeOE cmp (n + 1) : Net α (2 ^ (n + 1))) := by  -- induction
            rw [sortB_eq_sortOE n]
      _ = sortOE cmp (n + 1) := rfl                                -- definition of sortOE

/-! ## Step 2: the odd–even sorter refines to the Canfield–Williamson sorter -/

/-- **From `sortOE` to `sortQ`.** By the periodic law, `n + 1` passes of
`unriffle ⨾ mergeOE` sort just as Batcher's recursive sorter does; pushing the
`unriffle` into the merger gives Canfield and Williamson's merger. -/
theorem sortOE_eq_sortQ [LinearOrder α] : ∀ n, (sortOE cmp n : Net α (2 ^ n)) = sortQ cmp n
  | 0 => rfl
  | n + 1 =>
    calc (sortOE cmp (n + 1) : Net α (2 ^ (n + 1)))
        = (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) : Net α (2 ^ (n + 1))) :=
            -- the periodic law
            eq_of_sorts (sortOE_sorts (n + 1)) (periodicOE_sorts n)
      _ = (hrep (n + 1) (qfly cmp (n + 1)) : Net α (2 ^ (n + 1))) := by   -- qfly_eq: W3, W4
            rw [qfly_eq cmp_symm]; rfl
      _ = sortQ cmp (n + 1) := rfl                                      -- definition of sortQ

/-! ## Step 3: the Canfield–Williamson sorter refines to the balanced sorter -/

/-- **Merger exchange in the periodic sorters.** Each pass of a periodic sorter
halves the period of its input, whichever of Batcher's mergers it uses, so the
`n + 1` passes sort with either. -/
theorem periodic_merge_exchange [LinearOrder α] (n : Nat) :
    (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) : Net α (2 ^ (n + 1))) =
      hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeB cmp n) :=
  eq_of_sorts (periodicOE_sorts n) (periodicB_sorts n)

/-- **From `sortQ` to `sortV`.** Pull the `unriffle` out of Canfield and
Williamson's merger, exchange the odd–even merger for the bitonic one, and push
the `unriffle` back into Dowd et al.'s balanced merger. -/
theorem sortQ_eq_sortV [LinearOrder α] : ∀ n, (sortQ cmp n : Net α (2 ^ n)) = sortV cmp n
  | 0 => rfl
  | n + 1 =>
    calc (sortQ cmp (n + 1) : Net α (2 ^ (n + 1)))
        = (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeOE cmp (n + 1)) : Net α (2 ^ (n + 1))) := by
            exact sortQ_eq cmp_symm n                                       -- qfly_eq
      _ = (hrep (n + 1) (unriffle (m := 2 ^ n) ⨾ mergeB cmp n) : Net α (2 ^ (n + 1))) :=
                                                                            -- merger exchange
            periodic_merge_exchange n                                       -- in periodic passes
      _ = sortV cmp (n + 1) := by                                           -- vfly_eq: W5, a
            exact (sortV_eq cmp_symm n).symm                                -- butterfly ignores
                                                                            -- a reversal

/-! ## The paper's lemma, in the same calculus -/

/-- **The lemma of §6 of the paper:** `que (ilv f) = ilv (ilv f)`. -/
theorem que_ilv {k : Nat} (g : Net α k) : que (ilv g) = ilv (ilv g) := by
  funext x
  rw [eq_quad x]
  generalize evensIdx (evensIdx x) = P
  generalize evensIdx (oddsIdx x) = Q
  generalize oddsIdx (evensIdx x) = R
  generalize oddsIdx (oddsIdx x) = S
  have e₁ : ilv unriffle (quad P Q R S) = append (interleave P Q) (interleave R S) := by
    rw [ilv_apply, evensIdx_quad, oddsIdx_quad, unriffle_interleave, unriffle_interleave,
      interleave_append]
  simp only [que, seq_apply, e₁, two_append, ilv_apply, evensIdx_append,
    oddsIdx_append, evensIdx_interleave, oddsIdx_interleave, riffle_append, evensIdx_quad,
    oddsIdx_quad]

/-- **The paper's counterexample:** without the `unriffle` in front of each pass,
`n` bitonic mergers in series do not sort. -/
theorem bfly_hrep_counterexample :
    List.ofFn (hrep 2 (bfly (cmp : Net Bool 2) 2) (fun i => decide (i.val % 2 = 1))) =
      [false, true, false, true] := by
  decide

end Ruby.Vec
