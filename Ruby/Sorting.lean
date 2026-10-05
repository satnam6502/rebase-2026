import Ruby.Sorting.Derivation

/-!
# Four sorter cores, each refined into the next

The specification of a sorter on `2 ^ n` wires is `mergeSort`: the output lists
the input in non-decreasing order (`Sorts`). Batcher's bitonic sorter meets it
(`sortB_sorts`), and each of the other three cores is derived from the one
before by Bird–Meertens calculation (`Ruby.Sorting.Derivation`):

```
sortB (n+1)
  = two (sortB n) ⨾ mergeB n                       -- the reversal belongs to the merger
  = two (sortB n) ⨾ mergeOE (n+1)                  -- merger exchange on sorted halves
  = two (sortOE n) ⨾ mergeOE (n+1)                 -- induction
  = sortOE (n+1)

sortOE (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))          -- the periodic law
  = hrep (n+1) (qfly (n+1))                        -- qfly_eq: W3, W4
  = sortQ (n+1)

sortQ (n+1)
  = hrep (n+1) (unriffle ⨾ mergeOE (n+1))          -- qfly_eq
  = hrep (n+1) (unriffle ⨾ mergeB n)               -- merger exchange in periodic passes
  = sortV (n+1)                                    -- vfly_eq: W5, a butterfly ignores a reversal
```

The wiring steps (`sortB_succ`, `qfly_eq`, `vfly_eq`) hold for every symmetric
two-input cell. The merging steps hold for the comparator: Batcher's two
mergers agree on sorted halves (`merge_exchange`), and `n + 1` passes of
`unriffle ⨾ merge` sort for either merger, because each pass halves the period
of a `k`-sorted vector (`periodicOE_sorts`, `periodicB_sorts`).
-/

namespace Ruby.Vec

variable {α : Type} [LinearOrder α]

/-- **The refinement chain**: each sorter core is derived from the previous one,
at every degree. -/
theorem sorter_refinement (n : Nat) :
    (sortB cmp n : Net α (2 ^ n)) = sortOE cmp n ∧ (sortOE cmp n : Net α (2 ^ n)) = sortQ cmp n ∧
      (sortQ cmp n : Net α (2 ^ n)) = sortV cmp n :=
  ⟨sortB_eq_sortOE n, sortOE_eq_sortQ n, sortQ_eq_sortV n⟩

/-- So all four cores sort, starting from Batcher's bitonic sorter. -/
theorem four_sorters_sort (n : Nat) :
    Sorts (sortB cmp n : Net α (2 ^ n)) ∧ Sorts (sortOE cmp n : Net α (2 ^ n)) ∧
      Sorts (sortQ cmp n : Net α (2 ^ n)) ∧ Sorts (sortV cmp n : Net α (2 ^ n)) := by
  have hB := sortB_sorts (α := α) n
  obtain ⟨h1, h2, h3⟩ := sorter_refinement (α := α) n
  exact ⟨hB, h1 ▸ hB, h2 ▸ h1 ▸ hB, h3 ▸ h2 ▸ h1 ▸ hB⟩

end Ruby.Vec
