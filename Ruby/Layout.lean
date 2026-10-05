import Ruby.Core
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image

/-!
# Layout

The layout of a circuit is another structural interpretation of its term, in
the coordinates of a Xilinx 7-series relationally placed macro: `x` counts
slice columns and `y` counts LUT rows, four to a slice (so a LUT or flip-flop
at row `y` has `RLOC` row `y / 4` and BEL letter `A`–`D` from `y % 4`).

* `Prim.size`: a LUT or a flip-flop is one row high, a CARRY4 a whole slice;
* `Circuit.size`: `>->` places side by side, `>^>` and `‖` and `map` stack
  bottom to top, `>|>` overlays, and wiring takes no room;
* `Circuit.sites x y`: the slice resources (LUT, flip-flop or carry, at a
  column and a row) occupied by each primitive when the circuit is placed with
  its lower left corner at `(x, y)`.

Two general facts hold for every circuit: each occupied site lies inside the
bounding box (`sites_inBox`), and a circuit that only overlays parts using
different kinds of site occupies no site twice (`nodup_sites`). The sorters
inherit both, at every degree.
-/

namespace Ruby

open Shape

/-- The kinds of resource in a slice: four LUTs, eight flip-flops (one per LUT
row is used here) and one carry chain segment spanning the four rows. -/
inductive Site where
  | lut
  | ff
  | carry
  deriving DecidableEq, Repr

variable {a b c d : Shape}

namespace Prim

/-- The bounding box of a primitive: `(columns, LUT rows)`. -/
def size : Prim a b → Nat × Nat
  | .lut .. => (1, 1)
  | .fdce => (1, 1)
  | .carry4 => (1, 4)

/-- The sites a primitive occupies, relative to its lower left corner. -/
def footprint : Prim a b → List (Nat × Nat × Site)
  | .lut .. => [(0, 0, .lut)]
  | .fdce => [(0, 0, .ff)]
  | .carry4 => [(0, 0, .carry), (0, 1, .carry), (0, 2, .carry), (0, 3, .carry)]

theorem footprint_inBox (p : Prim a b) :
    ∀ q ∈ p.footprint, q.1 < p.size.1 ∧ q.2.1 < p.size.2 := by
  cases p <;> simp [footprint, size]

theorem footprint_nodup (p : Prim a b) : p.footprint.Nodup := by
  cases p <;> simp [footprint]

end Prim

namespace Circuit

/-- The bounding box of a circuit: `(columns, LUT rows)`. -/
def size : {a b : Shape} → Circuit a b → Nat × Nat
  | _, _, prim p => p.size
  | _, _, wire _ => (0, 0)
  | _, _, seq .beside r s => (r.size.1 + s.size.1, max r.size.2 s.size.2)
  | _, _, seq .below r s => (max r.size.1 s.size.1, r.size.2 + s.size.2)
  | _, _, seq .overlay r s => (max r.size.1 s.size.1, max r.size.2 s.size.2)
  | _, _, par r s => (max r.size.1 s.size.1, r.size.2 + s.size.2)
  | _, _, map n r => (r.size.1, n * r.size.2)

/-- The sites occupied by the circuit placed with its lower left corner at
`(x, y)`. -/
def sites : {a b : Shape} → Circuit a b → Nat → Nat → List (Nat × Nat × Site)
  | _, _, prim p, x, y => p.footprint.map fun q => (x + q.1, y + q.2.1, q.2.2)
  | _, _, wire _, _, _ => []
  | _, _, seq .beside r s, x, y => r.sites x y ++ s.sites (x + r.size.1) y
  | _, _, seq .below r s, x, y => r.sites x y ++ s.sites x (y + r.size.2)
  | _, _, seq .overlay r s, x, y => r.sites x y ++ s.sites x y
  | _, _, par r s, x, y => r.sites x y ++ s.sites x (y + r.size.2)
  | _, _, map n r, x, y => (List.range n).flatMap fun i => r.sites x (y + i * r.size.2)

/-- The kinds of site a circuit uses. -/
def kinds : {a b : Shape} → Circuit a b → List Site
  | _, _, prim p => p.footprint.map fun q => q.2.2
  | _, _, wire _ => []
  | _, _, seq _ r s => r.kinds ++ s.kinds
  | _, _, par r s => r.kinds ++ s.kinds
  | _, _, map _ r => r.kinds

/-- No two parts of the circuit are placed on the same sites: overlaid parts
use different kinds of site. -/
def NoOverlap : {a b : Shape} → Circuit a b → Prop
  | _, _, prim _ => True
  | _, _, wire _ => True
  | _, _, seq .overlay r s => r.NoOverlap ∧ s.NoOverlap ∧ ∀ k ∈ r.kinds, k ∉ s.kinds
  | _, _, seq .beside r s => r.NoOverlap ∧ s.NoOverlap
  | _, _, seq .below r s => r.NoOverlap ∧ s.NoOverlap
  | _, _, par r s => r.NoOverlap ∧ s.NoOverlap
  | _, _, map _ r => r.NoOverlap

/-- A site lies in the box with lower left corner `(x, y)` and size `sz`. -/
def InBox (x y : Nat) (sz : Nat × Nat) (q : Nat × Nat × Site) : Prop :=
  x ≤ q.1 ∧ q.1 < x + sz.1 ∧ y ≤ q.2.1 ∧ q.2.1 < y + sz.2

theorem mul_add_le {i n h : Nat} (hi : i < n) : i * h + h ≤ n * h := by
  have : (i + 1) * h ≤ n * h := Nat.mul_le_mul_right h hi
  rw [Nat.add_mul, Nat.one_mul] at this; exact this

/-- **Every occupied site lies inside the bounding box.** -/
theorem sites_inBox : {a b : Shape} → (c : Circuit a b) → (x y : Nat) →
    ∀ q ∈ c.sites x y, InBox x y c.size q
  | _, _, prim p, x, y, q, hq => by
      simp only [sites, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := p.footprint_inBox q' hq'
      simp only [InBox, size]; omega
  | _, _, wire _, _, _, q, hq => by simp [sites] at hq
  | _, _, seq .beside r s, x, y, q, hq => by
      simp only [sites, List.mem_append] at hq
      rcases hq with hq | hq
      · have := sites_inBox r x y q hq; simp only [InBox, size] at this ⊢; omega
      · have := sites_inBox s _ y q hq; simp only [InBox, size] at this ⊢; omega
  | _, _, seq .below r s, x, y, q, hq => by
      simp only [sites, List.mem_append] at hq
      rcases hq with hq | hq
      · have := sites_inBox r x y q hq; simp only [InBox, size] at this ⊢; omega
      · have := sites_inBox s x _ q hq; simp only [InBox, size] at this ⊢; omega
  | _, _, seq .overlay r s, x, y, q, hq => by
      simp only [sites, List.mem_append] at hq
      rcases hq with hq | hq
      · have := sites_inBox r x y q hq; simp only [InBox, size] at this ⊢; omega
      · have := sites_inBox s x y q hq; simp only [InBox, size] at this ⊢; omega
  | _, _, par r s, x, y, q, hq => by
      simp only [sites, List.mem_append] at hq
      rcases hq with hq | hq
      · have := sites_inBox r x y q hq; simp only [InBox, size] at this ⊢; omega
      · have := sites_inBox s x _ q hq; simp only [InBox, size] at this ⊢; omega
  | _, _, map n r, x, y, q, hq => by
      simp only [sites, List.mem_flatMap, List.mem_range] at hq
      obtain ⟨i, hi, hq⟩ := hq
      have := sites_inBox r x _ q hq
      have hle := mul_add_le (h := r.size.2) hi
      simp only [InBox, size] at this ⊢
      refine ⟨this.1, this.2.1, ?_, ?_⟩ <;> omega

theorem kind_mem_kinds : {a b : Shape} → (c : Circuit a b) → (x y : Nat) →
    ∀ q ∈ c.sites x y, q.2.2 ∈ c.kinds
  | _, _, prim p, x, y, q, hq => by
      simp only [sites, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      exact List.mem_map.mpr ⟨q', hq', rfl⟩
  | _, _, wire _, _, _, q, hq => by simp [sites] at hq
  | _, _, seq .beside r s, x, y, q, hq
  | _, _, seq .below r s, x, y, q, hq
  | _, _, seq .overlay r s, x, y, q, hq
  | _, _, par r s, x, y, q, hq => by
      simp only [sites, List.mem_append] at hq
      simp only [kinds, List.mem_append]
      rcases hq with hq | hq
      · exact Or.inl (kind_mem_kinds r _ _ q hq)
      · exact Or.inr (kind_mem_kinds s _ _ q hq)
  | _, _, map n r, x, y, q, hq => by
      simp only [sites, List.mem_flatMap, List.mem_range] at hq
      obtain ⟨i, _, hq⟩ := hq
      exact kind_mem_kinds r _ _ q hq

/-- **No site is occupied twice** by a circuit that only overlays parts using
different kinds of site. -/
theorem nodup_sites : {a b : Shape} → (c : Circuit a b) → c.NoOverlap → (x y : Nat) →
    (c.sites x y).Nodup
  | _, _, prim p, _, x, y => by
      simp only [sites]
      refine (p.footprint_nodup).map ?_
      intro q q' h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (Prod.ext (by omega) h.2.2)
  | _, _, wire _, _, _, _ => List.nodup_nil
  | _, _, seq .beside r s, h, x, y => by
      simp only [sites]
      refine List.nodup_append.mpr ⟨nodup_sites r h.1 x y, nodup_sites s h.2 _ y, ?_⟩
      intro q hq q' hq' heq
      have h1 := sites_inBox r x y q hq
      have h2 := sites_inBox s _ y q' hq'
      subst heq
      simp only [InBox] at h1 h2; omega
  | _, _, seq .below r s, h, x, y => by
      simp only [sites]
      refine List.nodup_append.mpr ⟨nodup_sites r h.1 x y, nodup_sites s h.2 x _, ?_⟩
      intro q hq q' hq' heq
      have h1 := sites_inBox r x y q hq
      have h2 := sites_inBox s x _ q' hq'
      subst heq
      simp only [InBox] at h1 h2; omega
  | _, _, seq .overlay r s, h, x, y => by
      simp only [sites]
      refine List.nodup_append.mpr ⟨nodup_sites r h.1 x y, nodup_sites s h.2.1 x y, ?_⟩
      intro q hq q' hq' heq
      subst heq
      exact h.2.2 _ (kind_mem_kinds r x y q hq) (kind_mem_kinds s x y q hq')
  | _, _, par r s, h, x, y => by
      simp only [sites]
      refine List.nodup_append.mpr ⟨nodup_sites r h.1 x y, nodup_sites s h.2 x _, ?_⟩
      intro q hq q' hq' heq
      have h1 := sites_inBox r x y q hq
      have h2 := sites_inBox s x _ q' hq'
      subst heq
      simp only [InBox] at h1 h2; omega
  | _, _, map n r, h, x, y => by
      simp only [sites]
      refine List.nodup_flatMap.mpr ⟨fun i _ => nodup_sites r h x _, ?_⟩
      refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := n))
      intro i j hi hj hij q hq hq'
      have h1 := sites_inBox r x _ q hq
      have h2 := sites_inBox r x _ q hq'
      have hle := mul_add_le (h := r.size.2) hij
      simp only [InBox] at h1 h2; omega

end Circuit

end Ruby

namespace Ruby.Circuit

open Shape

variable {a b : Shape}

/-- The number of LUTs in a circuit. -/
def lutCount : {a b : Shape} → Circuit a b → Nat
  | _, _, prim (.lut ..) => 1
  | _, _, prim _ => 0
  | _, _, wire _ => 0
  | _, _, seq _ r s => r.lutCount + s.lutCount
  | _, _, par r s => r.lutCount + s.lutCount
  | _, _, map n r => n * r.lutCount

/-- The LUT sites occupied by a circuit placed at `(x, y)`. -/
def lutSites (c : Circuit a b) (x y : Nat) : List (Nat × Nat × Site) :=
  (c.sites x y).filter fun q => q.2.2 = .lut

/-- `lutCount` counts the LUT sites of the placement, wherever it is placed. -/
theorem length_lutSites : {a b : Shape} → (c : Circuit a b) → (x y : Nat) →
    (c.lutSites x y).length = c.lutCount
  | _, _, prim (.lut ..), x, y => rfl
  | _, _, prim .fdce, x, y => rfl
  | _, _, prim .carry4, x, y => rfl
  | _, _, wire _, _, _ => rfl
  | _, _, seq .beside r s, x, y
  | _, _, seq .below r s, x, y
  | _, _, seq .overlay r s, x, y
  | _, _, par r s, x, y => by
      have hr := length_lutSites r
      have hs := length_lutSites s
      simp only [lutSites] at hr hs ⊢
      simp only [sites, List.filter_append, List.length_append, hr, hs, lutCount]
  | _, _, map n r, x, y => by
      have hr := length_lutSites r
      simp only [lutSites] at hr ⊢
      simp only [sites, List.filter_flatMap, List.length_flatMap, hr, lutCount]
      simp

end Ruby.Circuit

namespace Ruby.Circuit

open Shape

variable {a b : Shape}

/-- **Full LUT occupancy.** If a circuit occupies no site twice and has as many
LUTs as LUT sites in its bounding box, then every LUT site of the bounding box
is occupied. -/
theorem lut_sites_fill (c : Circuit a b) (x y : Nat) (hnd : (c.sites x y).Nodup)
    (hcount : c.lutCount = c.size.1 * c.size.2) :
    ∀ i < c.size.1, ∀ j < c.size.2, (x + i, y + j, Site.lut) ∈ c.sites x y := by
  classical
  intro i hi j hj
  set L := c.lutSites x y with hL
  have hLnd : L.Nodup := hnd.filter _
  let B : Finset (Nat × Nat × Site) :=
    ((Finset.range c.size.1) ×ˢ (Finset.range c.size.2)).image fun p => (x + p.1, y + p.2, .lut)
  have hsub : L.toFinset ⊆ B := by
    intro q hq
    rw [List.mem_toFinset] at hq
    have hq' := List.mem_filter.mp hq
    have hbox := sites_inBox c x y q hq'.1
    have hk : q.2.2 = .lut := by simpa using hq'.2
    simp only [InBox] at hbox
    simp only [B, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    refine ⟨(q.1 - x, q.2.1 - y), ⟨by omega, by omega⟩, ?_⟩
    obtain ⟨q1, q2, q3⟩ := q
    simp only at hk hbox ⊢
    subst hk
    simp only [Prod.mk.injEq, and_true]
    omega
  have hcardL : L.toFinset.card = c.size.1 * c.size.2 := by
    rw [List.toFinset_card_of_nodup hLnd, hL, length_lutSites, hcount]
  have hcardB : B.card ≤ c.size.1 * c.size.2 := by
    refine (Finset.card_image_le).trans ?_
    simp
  have heq : L.toFinset = B := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hmem : (x + i, y + j, Site.lut) ∈ B := by
    simp only [B, Finset.mem_image, Finset.mem_product, Finset.mem_range]
    exact ⟨(i, j), ⟨hi, hj⟩, rfl⟩
  rw [← heq, List.mem_toFinset] at hmem
  exact (List.mem_filter.mp hmem).1

end Ruby.Circuit
