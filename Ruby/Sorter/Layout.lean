import Ruby.Sorter.Cell
import Ruby.Layout
import Ruby.Latency

/-!
# The layout of the sorters

Facts about the placement of the hardware sorters, for every degree `n` and
every word width `4 (k + 1)`:

* the two-sorter cell is a `2 × 2 (k + 1)` block of slices (`size_twoSorter`);
* the butterfly mergers and the sorters are compact rectangles of cells: one
  column of `2 ^ (n - 1)` cells for each stage, side by side
  (`size_bitonicSorter`, `size_oddEvenSorter`, `size_balancedSorter`,
  `size_periodicSorter`);
* no slice resource is used twice (`noOverlap_*`, so `nodup_sites` applies) and
  every resource lies in the bounding box (`sites_inBox`);
* the bitonic and the balanced sorters use every LUT in their bounding box
  (`lutCount_bitonicSorter`, `lutCount_balancedSorter`).

The odd–even patterns place a one-slice-wide register column at each end of
their middle columns, so their columns keep the same height as a full column
of cells.
-/

namespace Ruby.Sorter

open Shape Circuit

/-! ## No overlaps -/

section NoOverlap

variable {a b c x y : Shape}

theorem noOverlap_idC : (idC : Circuit a a).NoOverlap := trivial

theorem noOverlap_parl {m : Nat} {r s : Circuit (.vec m a) (.vec m a)} (hr : r.NoOverlap)
    (hs : s.NoOverlap) : (parl r s).NoOverlap := ⟨trivial, ⟨hr, hs⟩, trivial⟩

theorem noOverlap_two {m : Nat} {r : Circuit (.vec m a) (.vec m a)} (hr : r.NoOverlap) :
    (two r).NoOverlap := noOverlap_parl hr hr

theorem noOverlap_ilv {m : Nat} {r : Circuit (.vec m a) (.vec m a)} (hr : r.NoOverlap) :
    (ilv r).NoOverlap := ⟨trivial, noOverlap_two hr, trivial⟩

theorem noOverlap_evens {m : Nat} {r : Circuit (.vec 2 a) (.vec 2 a)} (hr : r.NoOverlap) :
    (evens (m := m) r).NoOverlap := ⟨trivial, hr, trivial⟩

theorem noOverlap_midEvens {m : Nat} (h : 0 < m) {r : Circuit (.vec 2 a) (.vec 2 a)}
    {d : Circuit a a} (hr : r.NoOverlap) (hd : d.NoOverlap) :
    (midEvens h r d).NoOverlap := ⟨trivial, ⟨hd, ⟨hr, hd⟩⟩, trivial⟩

theorem noOverlap_vee {m : Nat} {r : Circuit (.vec m a) (.vec m a)} (hr : r.NoOverlap) :
    (vee r).NoOverlap := ⟨trivial, noOverlap_ilv hr, trivial⟩

theorem noOverlap_que {m : Nat} {r : Circuit (.vec (m * 2) a) (.vec (m * 2) a)} (hr : r.NoOverlap) :
    (que r).NoOverlap :=
  ⟨noOverlap_ilv (r := Circuit.unriffle) trivial, noOverlap_two hr,
    noOverlap_ilv (r := Circuit.riffle) trivial⟩

theorem noOverlap_hrep {r : Circuit a a} (hr : r.NoOverlap) : ∀ j, (hrep j r).NoOverlap
  | 0 => trivial
  | j + 1 => ⟨hr, noOverlap_hrep hr j⟩

theorem noOverlap_col {r : Circuit (.pair c x) (.pair y c)} (hr : r.NoOverlap) :
    ∀ n, (col n r).NoOverlap
  | 0 => trivial
  | n + 1 => ⟨trivial, ⟨hr, trivial⟩, trivial, ⟨trivial, noOverlap_col hr n⟩, trivial⟩

variable {r : Circuit (.vec 2 a) (.vec 2 a)} {d : Circuit a a}

theorem noOverlap_bfly (hr : r.NoOverlap) : ∀ n, (bfly r n).NoOverlap
  | 0 => trivial
  | 1 => hr
  | n + 2 => ⟨noOverlap_ilv (noOverlap_bfly hr (n + 1)), noOverlap_evens hr⟩

theorem noOverlap_mergeOE (hr : r.NoOverlap) (hd : d.NoOverlap) : ∀ n, (mergeOE r d n).NoOverlap
  | 0 => trivial
  | 1 => hr
  | n + 2 => ⟨noOverlap_ilv (noOverlap_mergeOE hr hd (n + 1)), noOverlap_midEvens _ hr hd⟩

theorem noOverlap_vfly (hr : r.NoOverlap) : ∀ n, (vfly r n).NoOverlap
  | 0 => trivial
  | 1 => hr
  | n + 2 => ⟨noOverlap_vee (noOverlap_vfly hr (n + 1)), noOverlap_evens hr⟩

theorem noOverlap_qfly (hr : r.NoOverlap) (hd : d.NoOverlap) : ∀ n, (qfly r d n).NoOverlap
  | 0 => trivial
  | 1 => hr
  | n + 2 => ⟨noOverlap_que (noOverlap_qfly hr hd (n + 1)), noOverlap_midEvens _ hr hd⟩

theorem noOverlap_sortB (hr : r.NoOverlap) : ∀ n, (sortB r n).NoOverlap
  | 0 => trivial
  | n + 1 => ⟨noOverlap_parl (noOverlap_sortB hr n) ⟨noOverlap_sortB hr n, trivial⟩,
      noOverlap_bfly hr (n + 1)⟩

theorem noOverlap_sortOE (hr : r.NoOverlap) (hd : d.NoOverlap) : ∀ n, (sortOE r d n).NoOverlap
  | 0 => trivial
  | n + 1 => ⟨noOverlap_two (noOverlap_sortOE hr hd n), noOverlap_mergeOE hr hd (n + 1)⟩

end NoOverlap

theorem noOverlap_geTile : geTile.NoOverlap := by
  simp [geTile, NoOverlap, kinds, xnorLut, snd, idC, Prim.footprint]

theorem noOverlap_muxReg (w : Nat) : (muxReg w).NoOverlap :=
  ⟨trivial, trivial, trivial, by simp [kinds, muxLut, reg, Prim.footprint]⟩

theorem noOverlap_twoSorter (k : Nat) : (twoSorter k).NoOverlap :=
  ⟨trivial, ⟨⟨trivial, ⟨⟨trivial, noOverlap_col noOverlap_geTile k, trivial⟩, trivial⟩,
      noOverlap_muxReg _⟩, ⟨trivial, ⟨⟨trivial, noOverlap_col noOverlap_geTile k, trivial⟩, trivial⟩,
      noOverlap_muxReg _⟩⟩, trivial⟩

theorem noOverlap_delayW (w : Nat) : (delayW w).NoOverlap := trivial

/-- **No resource of the bitonic sorter is used twice**, at every degree. -/
theorem nodup_bitonicSorter (k n x y : Nat) : ((bitonicSorter k n).sites x y).Nodup :=
  nodup_sites _ (noOverlap_sortB (noOverlap_twoSorter k) n) x y

theorem nodup_oddEvenSorter (k n x y : Nat) : ((oddEvenSorter k n).sites x y).Nodup :=
  nodup_sites _ (noOverlap_sortOE (noOverlap_twoSorter k) (noOverlap_delayW _) n) x y

theorem nodup_balancedSorter (k n x y : Nat) : ((balancedSorter k n).sites x y).Nodup :=
  nodup_sites _ (noOverlap_hrep (noOverlap_vfly (noOverlap_twoSorter k) n) n) x y

theorem nodup_periodicSorter (k n x y : Nat) : ((periodicSorter k n).sites x y).Nodup :=
  nodup_sites _ (noOverlap_hrep (noOverlap_qfly (noOverlap_twoSorter k) (noOverlap_delayW _) n) n)
    x y

end Ruby.Sorter

namespace Ruby.Sorter

open Shape Circuit

/-! ## Bounding boxes -/

section Size

variable {a : Shape}

@[simp] theorem size_idC : (idC : Circuit a a).size = (0, 0) := rfl

@[simp] theorem size_rev {n : Nat} : (Circuit.rev : Circuit (.vec n a) (.vec n a)).size = (0, 0) := rfl

theorem size_parl {m : Nat} (r s : Circuit (.vec m a) (.vec m a)) :
    (parl r s).size = (max r.size.1 s.size.1, r.size.2 + s.size.2) := by
  simp [parl, Circuit.size]

theorem size_two {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (two r).size = (r.size.1, 2 * r.size.2) := by
  simp [two, size_parl, two_mul]

theorem size_ilv {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (ilv r).size = (r.size.1, 2 * r.size.2) := by
  simp [ilv, Circuit.size, size_two]

theorem size_evens {m : Nat} (r : Circuit (.vec 2 a) (.vec 2 a)) :
    (evens (m := m) r).size = (r.size.1, m * r.size.2) := by
  simp [evens, Circuit.size]

theorem size_midEvens {m : Nat} (h : 0 < m) (r : Circuit (.vec 2 a) (.vec 2 a)) (d : Circuit a a)
    (e : Nat) (hr : r.size.2 = 2 * e) (hd : d.size.2 = e) (hw : d.size.1 ≤ r.size.1) :
    (midEvens h r d).size = (r.size.1, m * r.size.2) := by
  simp only [midEvens, Circuit.size, Nat.zero_add, Nat.add_zero, Nat.zero_max, Nat.max_zero, hr, hd]
  refine Prod.ext ?_ ?_
  · simp only; omega
  · simp only
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring

theorem size_vee {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (vee r).size = (r.size.1, 2 * r.size.2) := by
  simp [vee, Circuit.size, Circuit.alt, size_ilv]

theorem size_que {m : Nat} (r : Circuit (.vec (m * 2) a) (.vec (m * 2) a)) :
    (que r).size = (r.size.1, 2 * r.size.2) := by
  simp [que, Circuit.size, size_ilv, size_two, Circuit.unriffle, Circuit.riffle]

theorem size_hrep (r : Circuit a a) (hw : 0 < r.size.1) : ∀ j,
    (hrep (j + 1) r).size = ((j + 1) * r.size.1, r.size.2)
  | 0 => by simp [hrep, Circuit.size]
  | j + 1 => by
      rw [hrep, Circuit.size, size_hrep r hw j]
      refine Prod.ext ?_ ?_
      · simp only; ring
      · simp

variable {r : Circuit (.vec 2 a) (.vec 2 a)} {d : Circuit a a}

theorem size_bfly : ∀ n, (bfly r (n + 1)).size = ((n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by simp [bfly]
  | n + 1 => by
      change (ilv (bfly r (n + 1)) >-> evens r).size = _
      rw [Circuit.size, size_ilv, size_evens, size_bfly n]
      refine Prod.ext ?_ ?_
      · simp only; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (by rw [Nat.mul_comm 2]; exact le_of_eq (by ring))]
        ring

theorem size_mergeOE (e : Nat) (hr : r.size.2 = 2 * e) (hd : d.size.2 = e)
    (hw : d.size.1 ≤ r.size.1) : ∀ n, (mergeOE r d (n + 1)).size = ((n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by simp [mergeOE]
  | n + 1 => by
      change (ilv (mergeOE r d (n + 1)) >-> midEvens (Nat.two_pow_pos (n + 1)) r d).size = _
      rw [Circuit.size, size_ilv, size_midEvens _ r d e hr hd hw, size_mergeOE e hr hd hw n]
      refine Prod.ext ?_ ?_
      · simp only; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (le_of_eq (by ring))]; ring

theorem size_vfly : ∀ n, (vfly r (n + 1)).size = ((n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by simp [vfly]
  | n + 1 => by
      change (vee (vfly r (n + 1)) >-> evens r).size = _
      rw [Circuit.size, size_vee, size_evens, size_vfly n]
      refine Prod.ext ?_ ?_
      · simp only; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (le_of_eq (by ring))]; ring

theorem size_qfly (e : Nat) (hr : r.size.2 = 2 * e) (hd : d.size.2 = e)
    (hw : d.size.1 ≤ r.size.1) : ∀ n, (qfly r d (n + 1)).size = ((n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by simp [qfly]
  | n + 1 => by
      change (que (m := 2 ^ n) (qfly r d (n + 1)) >-> midEvens (Nat.two_pow_pos (n + 1)) r d).size = _
      rw [Circuit.size, size_que (m := 2 ^ n) (qfly r d (n + 1)),
        size_midEvens (m := 2 ^ n * 2) (Nat.two_pow_pos (n + 1)) r d e hr hd hw]
      erw [size_qfly e hr hd hw n]
      refine Prod.ext ?_ ?_
      · simp only; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (le_of_eq (by ring))]; ring

theorem size_sortB : ∀ n, (sortB r (n + 1)).size = (tri (n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by
      change (parl idC (idC >-> Circuit.rev) >-> bfly r 1).size = _
      simp [Circuit.size, size_parl, bfly, tri, Circuit.rev]
  | n + 1 => by
      have h1 := size_parl (sortB r (n + 1)) (sortB r (n + 1) >-> Circuit.rev)
      have h2 := size_bfly (r := r) (n + 1)
      have h3 := size_sortB n
      change (parl (sortB r (n + 1)) (sortB r (n + 1) >-> Circuit.rev) >->
        bfly r (n + 1 + 1)).size = _
      simp only [Circuit.size, h1, h3, size_rev, Nat.add_zero, Nat.max_zero, max_self]
      erw [h2]
      refine Prod.ext ?_ ?_
      · simp only [tri]; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (le_of_eq (by ring))]; ring

theorem size_sortOE (e : Nat) (hr : r.size.2 = 2 * e) (hd : d.size.2 = e)
    (hw : d.size.1 ≤ r.size.1) :
    ∀ n, (sortOE r d (n + 1)).size = (tri (n + 1) * r.size.1, 2 ^ n * r.size.2)
  | 0 => by
      change (two idC >-> mergeOE r d 1).size = _
      simp [Circuit.size, size_two, mergeOE, tri]
  | n + 1 => by
      have h1 := size_two (sortOE r d (n + 1))
      have h2 := size_mergeOE e hr hd hw (n + 1)
      have h3 := size_sortOE e hr hd hw n
      change (two (sortOE r d (n + 1)) >-> mergeOE r d (n + 1 + 1)).size = _
      simp only [Circuit.size, h1, h3]
      erw [h2]
      refine Prod.ext ?_ ?_
      · simp only [tri]; ring
      · simp only [Nat.pow_succ]; rw [max_eq_left (le_of_eq (by ring))]; ring

end Size

/-! ### The cell -/

theorem size_geTile : geTile.size = (1, 4) := rfl

theorem size_col_geTile : ∀ k, (col (k + 1) geTile).size = (1, 4 * (k + 1))
  | 0 => rfl
  | k + 1 => by
      have ih := size_col_geTile k
      change (wire _ >-> (fst geTile >^> (wire _ >-> snd (col (k + 1) geTile) >-> wire _))).size = _
      simp only [Circuit.size, fst, snd, size_idC, size_geTile, ih]
      refine Prod.ext ?_ ?_ <;> (simp; try omega)

theorem size_geC (k : Nat) : (geC (k + 1)).size = (1, 4 * (k + 1)) := by
  simp [geC, Circuit.size, size_col_geTile]

theorem size_muxReg (w : Nat) : (muxReg w).size = (1, w) := by
  simp [muxReg, Circuit.size, muxLut, reg, Prim.size]

/-- The two-sorter on words of `4 (k + 1)` bits is `2` slice columns wide and
`8 (k + 1)` LUT rows (`2 (k + 1)` slices) high. -/
theorem size_twoSorter (k : Nat) : (twoSorter (k + 1)).size = (2, 8 * (k + 1)) := by
  simp only [twoSorter, halfMin, halfMax, Circuit.size, fst, size_idC, size_geC, size_muxReg]
  refine Prod.ext ?_ ?_ <;> (simp; try omega)

theorem size_delayW (w : Nat) : (delayW w).size = (1, w) := by
  simp [delayW, Circuit.size, reg, Prim.size]

/-! ### The sorters

A sorter of `2 ^ (n + 1)` words is a rectangle of cells: one column of `2 ^ n`
cells per stage. -/

theorem size_bitonicSorter (k n : Nat) :
    (bitonicSorter (k + 1) (n + 1)).size = (2 * tri (n + 1), 2 ^ n * (8 * (k + 1))) := by
  rw [bitonicSorter, size_sortB, size_twoSorter, Nat.mul_comm (tri _)]

theorem size_oddEvenSorter (k n : Nat) :
    (oddEvenSorter (k + 1) (n + 1)).size = (2 * tri (n + 1), 2 ^ n * (8 * (k + 1))) := by
  rw [oddEvenSorter, size_sortOE (4 * (k + 1)), size_twoSorter, Nat.mul_comm (tri _)]
  · rw [size_twoSorter]; ring
  · rw [size_delayW]; ring
  · rw [size_delayW, size_twoSorter]; omega

theorem size_balancedSorter (k n : Nat) :
    (balancedSorter (k + 1) (n + 1)).size = (2 * ((n + 1) * (n + 1)), 2 ^ n * (8 * (k + 1))) := by
  rw [balancedSorter, sortV, size_hrep _ (by rw [size_vfly, size_twoSorter]; simp only; omega),
    size_vfly, size_twoSorter]
  refine Prod.ext ?_ rfl
  simp only; ring

theorem size_periodicSorter (k n : Nat) :
    (periodicSorter (k + 1) (n + 1)).size = (2 * ((n + 1) * (n + 1)), 2 ^ n * (8 * (k + 1))) := by
  have hq := size_qfly (r := twoSorter (k + 1)) (d := delayW ((k + 1) * 4)) (4 * (k + 1))
    (by rw [size_twoSorter]; ring) (by rw [size_delayW]; ring)
    (by rw [size_delayW, size_twoSorter]; omega) n
  rw [periodicSorter, sortQ, size_hrep _ (by rw [hq, size_twoSorter]; simp only; omega), hq,
    size_twoSorter]
  refine Prod.ext ?_ rfl
  simp only; ring

end Ruby.Sorter

namespace Ruby.Sorter

open Shape Circuit

/-! ## Every LUT of the bounding box is used -/

section Count

variable {a : Shape}

theorem lutCount_parl {m : Nat} (r s : Circuit (.vec m a) (.vec m a)) :
    (parl r s).lutCount = r.lutCount + s.lutCount := by
  simp [parl, lutCount]

theorem lutCount_two {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (two r).lutCount = 2 * r.lutCount := by
  simp [two, lutCount_parl, two_mul]

theorem lutCount_ilv {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (ilv r).lutCount = 2 * r.lutCount := by
  simp [ilv, lutCount, lutCount_two]

theorem lutCount_evens {m : Nat} (r : Circuit (.vec 2 a) (.vec 2 a)) :
    (evens (m := m) r).lutCount = m * r.lutCount := by
  simp [evens, lutCount]

theorem lutCount_vee {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (vee r).lutCount = 2 * r.lutCount := by
  simp [vee, lutCount, Circuit.alt, lutCount_ilv]

theorem lutCount_hrep (r : Circuit a a) : ∀ j, (hrep j r).lutCount = j * r.lutCount
  | 0 => by simp [hrep, idC, lutCount]
  | j + 1 => by rw [hrep, lutCount, lutCount_hrep r j]; ring

variable {r : Circuit (.vec 2 a) (.vec 2 a)}

theorem lutCount_bfly : ∀ n, (bfly r (n + 1)).lutCount = (n + 1) * 2 ^ n * r.lutCount
  | 0 => by simp [bfly]
  | n + 1 => by
      change (ilv (bfly r (n + 1)) >-> evens r).lutCount = _
      rw [lutCount, lutCount_ilv, lutCount_evens, lutCount_bfly n, Nat.pow_succ]; ring

theorem lutCount_vfly : ∀ n, (vfly r (n + 1)).lutCount = (n + 1) * 2 ^ n * r.lutCount
  | 0 => by simp [vfly]
  | n + 1 => by
      change (vee (vfly r (n + 1)) >-> evens r).lutCount = _
      rw [lutCount, lutCount_vee, lutCount_evens, lutCount_vfly n, Nat.pow_succ]; ring

theorem lutCount_sortB : ∀ n, (sortB r (n + 1)).lutCount = tri (n + 1) * 2 ^ n * r.lutCount
  | 0 => by
      change (parl idC (idC >-> Circuit.rev) >-> bfly r 1).lutCount = _
      simp [lutCount, lutCount_parl, idC, Circuit.rev, bfly, tri]
  | n + 1 => by
      have h1 := lutCount_parl (sortB r (n + 1)) (sortB r (n + 1) >-> Circuit.rev)
      have h3 := lutCount_sortB n
      change (parl (sortB r (n + 1)) (sortB r (n + 1) >-> Circuit.rev) >->
        bfly r (n + 1 + 1)).lutCount = _
      have hrev : (Circuit.rev : Circuit (.vec (2 ^ (n + 1)) a) (.vec (2 ^ (n + 1)) a)).lutCount = 0 :=
        rfl
      simp only [lutCount, h1, h3, hrev]
      erw [lutCount_bfly (n + 1)]
      simp only [tri, Nat.pow_succ, Nat.add_zero]; ring

end Count

theorem lutCount_col_geTile : ∀ k, (col k geTile).lutCount = 4 * k
  | 0 => rfl
  | k + 1 => by
      change (wire _ >-> (fst geTile >^> (wire _ >-> snd (col k geTile) >-> wire _))).lutCount = _
      have hg : geTile.lutCount = 4 := rfl
      simp only [lutCount, fst, snd, idC, lutCount_col_geTile k, hg]
      omega

theorem lutCount_twoSorter (k : Nat) : (twoSorter k).lutCount = 16 * k := by
  simp only [twoSorter, halfMin, halfMax, geC, muxReg, lutCount, fst, idC, lutCount_col_geTile,
    muxLut, reg]
  ring

/-- **The bitonic sorter uses every LUT in its bounding box**, at every degree. -/
theorem lutCount_bitonicSorter (k n : Nat) :
    (bitonicSorter (k + 1) (n + 1)).lutCount =
      (bitonicSorter (k + 1) (n + 1)).size.1 * (bitonicSorter (k + 1) (n + 1)).size.2 := by
  rw [size_bitonicSorter, bitonicSorter, lutCount_sortB, lutCount_twoSorter]
  ring

/-- **The balanced sorter uses every LUT in its bounding box**, at every degree. -/
theorem lutCount_balancedSorter (k n : Nat) :
    (balancedSorter (k + 1) (n + 1)).lutCount =
      (balancedSorter (k + 1) (n + 1)).size.1 * (balancedSorter (k + 1) (n + 1)).size.2 := by
  rw [size_balancedSorter, balancedSorter, sortV, lutCount_hrep, lutCount_vfly, lutCount_twoSorter]
  ring

/-- Placed anywhere, the bitonic sorter occupies every LUT site of its bounding
box: the layout is a dense rectangle. -/
theorem bitonicSorter_dense (k n x y : Nat) :
    ∀ i < (bitonicSorter (k + 1) (n + 1)).size.1, ∀ j < (bitonicSorter (k + 1) (n + 1)).size.2,
      (x + i, y + j, Site.lut) ∈ (bitonicSorter (k + 1) (n + 1)).sites x y :=
  lut_sites_fill _ x y (nodup_bitonicSorter _ _ x y) (lutCount_bitonicSorter k n)

/-- Placed anywhere, the balanced sorter occupies every LUT site of its bounding
box. -/
theorem balancedSorter_dense (k n x y : Nat) :
    ∀ i < (balancedSorter (k + 1) (n + 1)).size.1, ∀ j < (balancedSorter (k + 1) (n + 1)).size.2,
      (x + i, y + j, Site.lut) ∈ (balancedSorter (k + 1) (n + 1)).sites x y :=
  lut_sites_fill _ x y (nodup_balancedSorter _ _ x y) (lutCount_balancedSorter k n)

end Ruby.Sorter
