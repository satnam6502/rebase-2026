import Ruby.Core
import Ruby.Sorting.Networks

/-!
# Ruby combinators

Wiring and repetition combinators built from the core constructors. Each has a
geometric reading (wiring takes no area; `‖` stacks bottom to top; `>->`
places left to right; `>^>` stacks a serial composition) and its combinational
semantics is the corresponding vector network of `Ruby.Vec`
(`eval_two`, `eval_ilv`, …).

The butterfly-shaped networks `bfly`, `mergeOE`, `vfly`, `qfly` and the four
sorters are defined here over an arbitrary two-input cell `r`; the odd–even
patterns also take a one-input delay `d` for the wires that bypass the middle
column, so that a pipelined cell keeps every path the same length.
-/

namespace Ruby

open Shape Vec

variable {a b c x y : Shape}

/-! ## Wiring -/

namespace Wiring

def id : Wiring a a := ⟨fun _ v => v, by intros; rfl⟩

def swap : Wiring (.pair a b) (.pair b a) := ⟨fun _ v => (v.2, v.1), by intros; rfl⟩

def fork : Wiring a (.pair a a) := ⟨fun _ v => (v, v), by intros; rfl⟩

/-- Split a vector into its halves. -/
def split {m : Nat} : Wiring (.vec (m * 2) a) (.pair (.vec m a) (.vec m a)) :=
  ⟨fun _ v => (lo v, hi v), by intros; rfl⟩

/-- Concatenate two halves. -/
def join {m : Nat} : Wiring (.pair (.vec m a) (.vec m a)) (.vec (m * 2) a) :=
  ⟨fun _ v => append v.1 v.2, by
    intros; funext j; simp only [Shape.map_vec, Shape.map_pair, append]; split_ifs <;> rfl⟩

def riffle {m : Nat} : Wiring (.vec (m * 2) a) (.vec (m * 2) a) :=
  ⟨fun _ v => Vec.riffle v, by
    intros; funext j; simp only [Shape.map_vec, Vec.riffle, interleave]; split_ifs <;> rfl⟩

def unriffle {m : Nat} : Wiring (.vec (m * 2) a) (.vec (m * 2) a) :=
  ⟨fun _ v => Vec.unriffle v, by
    intros; funext j; simp only [Shape.map_vec, Vec.unriffle, append]; split_ifs <;> rfl⟩

def rev {n : Nat} : Wiring (.vec n a) (.vec n a) := ⟨fun _ v => Vec.rev v, by intros; rfl⟩

def alt {m : Nat} : Wiring (.vec (m * 2) a) (.vec (m * 2) a) := ⟨fun _ v => Vec.alt v, by intros; rfl⟩

/-- Group adjacent pairs. -/
def pairs {m : Nat} : Wiring (.vec (m * 2) a) (.vec m (.vec 2 a)) :=
  ⟨fun _ v => Vec.pairs v, by intros; rfl⟩

def unpairs {m : Nat} : Wiring (.vec m (.vec 2 a)) (.vec (m * 2) a) :=
  ⟨fun _ v => Vec.unpairs v, by intros; rfl⟩

/-- Separate the first and last wires from the middle pairs `(2 i + 1, 2 i + 2)`. -/
def midSplit {m : Nat} (h : 0 < m) :
    Wiring (.vec (m * 2) a) (.pair a (.pair (.vec (m - 1) (.vec 2 a)) a)) :=
  ⟨fun _ v => (v ⟨0, by omega⟩,
      (fun i j => v ⟨2 * i.val + 1 + j.val, by have := i.isLt; have := j.isLt; omega⟩,
        v ⟨m * 2 - 1, by omega⟩)), by intros; rfl⟩

/-- Reassemble the first wire, the middle pairs and the last wire. -/
def midJoin {m : Nat} : Wiring (.pair a (.pair (.vec (m - 1) (.vec 2 a)) a)) (.vec (m * 2) a) :=
  ⟨fun _ v j => if h0 : j.val = 0 then v.1 else if h : j.val = m * 2 - 1 then v.2.2
      else v.2.1 ⟨(j.val - 1) / 2, by have := j.isLt; omega⟩ ⟨(j.val - 1) % 2, by omega⟩, by
    intros; funext j; simp only [Shape.map_vec, Shape.map_pair]; split_ifs <;> rfl⟩

end Wiring

/-! ## Combinators -/

namespace Circuit

/-- The identity: no hardware, no area. -/
def idC : Circuit a a := wire Wiring.id

/-- Apply `r` to the first component of a pair. -/
def fst (r : Circuit a b) : Circuit (.pair a c) (.pair b c) := r ‖ idC

/-- Apply `r` to the second component of a pair. -/
def snd (r : Circuit b c) : Circuit (.pair a b) (.pair a c) := idC ‖ r

/-- `r` on the first half and `s` on the second, `r` below `s`. -/
def parl {m : Nat} (r s : Circuit (.vec m a) (.vec m a)) : Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  wire Wiring.split >-> (r ‖ s) >-> wire Wiring.join

/-- Two copies of `r`, one on each half. -/
def two {m : Nat} (r : Circuit (.vec m a) (.vec m a)) : Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  parl r r

/-- `r` on the even positions and on the odd positions. -/
def ilv {m : Nat} (r : Circuit (.vec m a) (.vec m a)) : Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  wire Wiring.unriffle >-> two r >-> wire Wiring.riffle

/-- A column of the two-input cell `r` on the adjacent pairs. -/
def evens {m : Nat} (r : Circuit (.vec 2 a) (.vec 2 a)) : Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  wire Wiring.pairs >-> map m r >-> wire Wiring.unpairs

/-- The middle column: `r` on the pairs `(2 i + 1, 2 i + 2)`, and the delay `d` on
the first and last wires, which keeps every path equally long. The delays are
placed below and above the cells. -/
def midEvens {m : Nat} (h : 0 < m) (r : Circuit (.vec 2 a) (.vec 2 a)) (d : Circuit a a) :
    Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  wire (Wiring.midSplit h) >-> (d ‖ (map (m - 1) r ‖ d)) >-> wire Wiring.midJoin

def rev {n : Nat} : Circuit (.vec n a) (.vec n a) := wire Wiring.rev

def alt {m : Nat} : Circuit (.vec (m * 2) a) (.vec (m * 2) a) := wire Wiring.alt

def unriffle {m : Nat} : Circuit (.vec (m * 2) a) (.vec (m * 2) a) := wire Wiring.unriffle

def riffle {m : Nat} : Circuit (.vec (m * 2) a) (.vec (m * 2) a) := wire Wiring.riffle

/-- Dowd et al.'s pattern. -/
def vee {m : Nat} (r : Circuit (.vec m a) (.vec m a)) : Circuit (.vec (m * 2) a) (.vec (m * 2) a) :=
  alt >-> ilv r >-> alt

/-- Canfield and Williamson's pattern. -/
def que {m : Nat} (r : Circuit (.vec (m * 2) a) (.vec (m * 2) a)) :
    Circuit (.vec (m * 2 * 2) a) (.vec (m * 2 * 2) a) :=
  ilv unriffle >-> two r >-> ilv riffle

/-- `k` copies of `r` in series, left to right. -/
def hrep : Nat → Circuit a a → Circuit a a
  | 0, _ => idC
  | k + 1, r => r >-> hrep k r

/-- A column of `n` tiles whose carry runs upwards: Ruby's `col`. Tile `0` is at
the bottom. -/
def col : (n : Nat) → Circuit (.pair c x) (.pair y c) → Circuit (.pair c (.vec n x)) (.pair (.vec n y) c)
  | 0, _ => wire ⟨fun _ v => (fun i => i.elim0, v.1), by
      intros; refine Prod.ext ?_ rfl; funext i; exact i.elim0⟩
  | n + 1, r =>
      wire ⟨fun _ v => ((v.1, v.2 0), fun i => v.2 i.succ), by intros; rfl⟩ >->
        (fst r >^>
          (wire ⟨fun _ v => (v.1.1, (v.1.2, v.2)), by intros; rfl⟩ >-> snd (col n r) >->
            wire ⟨fun _ v => (Fin.cons v.1 v.2.1, v.2.2), by
              intros; refine Prod.ext ?_ rfl; funext i; refine Fin.cases rfl (fun _ => rfl) i⟩))

/-! ## Butterfly networks and sorters over a two-input cell -/

variable (r : Circuit (.vec 2 a) (.vec 2 a)) (d : Circuit a a)

/-- Batcher's bitonic merger: a butterfly. -/
def bfly : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | 1 => r
  | n + 2 => ilv (bfly (n + 1)) >-> evens r

/-- Batcher's odd–even merger. -/
def mergeOE : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | 1 => r
  | n + 2 => ilv (mergeOE (n + 1)) >-> midEvens (Nat.two_pow_pos (n + 1)) r d

/-- Dowd et al.'s balanced merger. -/
def vfly : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | 1 => r
  | n + 2 => vee (vfly (n + 1)) >-> evens r

/-- Canfield and Williamson's merger. -/
def qfly : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | 1 => r
  | n + 2 => que (m := 2 ^ n) (qfly (n + 1)) >-> midEvens (Nat.two_pow_pos (n + 1)) r d

/-- Batcher's bitonic sorter. -/
def sortB : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | n + 1 => parl (sortB n) (sortB n >-> rev) >-> bfly r (n + 1)

/-- Batcher's odd–even merge sorter. -/
def sortOE : (n : Nat) → Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a)
  | 0 => idC
  | n + 1 => two (sortOE n) >-> mergeOE r d (n + 1)

/-- The periodic sorter of balanced mergers. -/
def sortV (n : Nat) : Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a) := hrep n (vfly r n)

/-- The periodic sorter of Canfield–Williamson mergers. -/
def sortQ (n : Nat) : Circuit (.vec (2 ^ n) a) (.vec (2 ^ n) a) := hrep n (qfly r d n)

/-! ## Behaviour: the circuits compute the vector networks -/

variable {r d}

@[simp] theorem eval_idC (v : a.Val Bool) : (idC : Circuit a a).eval v = v := rfl

theorem eval_parl {m : Nat} (r s : Circuit (.vec m a) (.vec m a)) :
    (parl (m := m) r s).eval = Vec.parl r.eval s.eval := rfl

theorem eval_two {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (two r).eval = Vec.two r.eval := rfl

theorem eval_ilv {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (ilv r).eval = Vec.ilv r.eval := rfl

theorem eval_evens {m : Nat} (r : Circuit (.vec 2 a) (.vec 2 a)) :
    (evens (m := m) r).eval = Vec.evens r.eval := rfl

theorem eval_midEvens {m : Nat} (h : 0 < m) (r : Circuit (.vec 2 a) (.vec 2 a)) (d : Circuit a a)
    (hd : ∀ v, d.eval v = v) : (midEvens h r d).eval = Vec.midEvens (m := m) r.eval := by
  funext v j
  simp only [midEvens, eval_seq, eval_wire, eval_par, eval_map, Wiring.midSplit, Wiring.midJoin,
    hd, Vec.midEvens]
  by_cases h0 : j.val = 0
  · have he : IsEnd j := Or.inl h0
    simp only [h0, ↓reduceIte, ↓reduceDIte, he]
    congr 1; apply Fin.ext; simp only; omega
  · by_cases hl : j.val = m * 2 - 1
    · have he : IsEnd j := Or.inr hl
      have hl' : m * 2 - 1 ≠ 0 := by omega
      simp only [hl, hl', ↓reduceIte, ↓reduceDIte, he]
      congr 1; apply Fin.ext; simp only; omega
    · have he : ¬ IsEnd j := by unfold IsEnd; omega
      simp only [h0, hl, ↓reduceIte, ↓reduceDIte, he]
      rw [midPair_eq_of_not_end _ _ (by omega)]

theorem eval_vee {m : Nat} (r : Circuit (.vec m a) (.vec m a)) :
    (vee r).eval = Vec.vee r.eval := rfl

theorem eval_que {m : Nat} (r : Circuit (.vec (m * 2) a) (.vec (m * 2) a)) :
    (que r).eval = Vec.que r.eval := rfl

theorem eval_hrep {N : Nat} (r : Circuit (.vec N a) (.vec N a)) :
    ∀ k, (hrep k r).eval = Vec.hrep k r.eval
  | 0 => rfl
  | k + 1 => by funext v; simp only [hrep, eval_seq, eval_hrep r k]; rfl

theorem eval_bfly : ∀ n, (bfly r n).eval = Vec.bfly r.eval n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      funext v
      change (evens r).eval ((ilv (bfly r (n + 1))).eval v) = _
      rw [eval_evens, eval_ilv, eval_bfly (n + 1)]; rfl

theorem eval_mergeOE (hd : ∀ v, d.eval v = v) : ∀ n, (mergeOE r d n).eval = Vec.mergeOE r.eval n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      funext v
      change (midEvens _ r d).eval ((ilv (mergeOE r d (n + 1))).eval v) = _
      rw [eval_midEvens _ r d hd, eval_ilv, eval_mergeOE hd (n + 1)]; rfl

theorem eval_vfly : ∀ n, (vfly r n).eval = Vec.vfly r.eval n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      funext v
      change (evens r).eval ((vee (vfly r (n + 1))).eval v) = _
      rw [eval_evens, eval_vee, eval_vfly (n + 1)]; rfl

theorem eval_qfly (hd : ∀ v, d.eval v = v) : ∀ n, (qfly r d n).eval = Vec.qfly r.eval n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      funext v
      have h1 := congrFun (eval_midEvens (m := 2 ^ n * 2) (Nat.two_pow_pos (n + 1)) r d hd)
        ((que (m := 2 ^ n) (qfly r d (n + 1))).eval v)
      refine h1.trans ?_
      exact congrArg (fun F => Vec.midEvens (m := 2 ^ (n + 1)) r.eval (Vec.que (m := 2 ^ n) F v))
        (eval_qfly hd (n + 1))

theorem eval_sortB : ∀ n, (sortB r n).eval = Vec.sortB r.eval n
  | 0 => rfl
  | n + 1 => by
      funext v
      have hs : (sortB r n >-> rev).eval = (Vec.sortB r.eval n ⨾ Vec.rev) := by
        funext w; simp only [eval_seq, eval_sortB n]; rfl
      change (bfly r (n + 1)).eval ((parl (sortB r n) (sortB r n >-> rev)).eval v) = _
      rw [eval_bfly, eval_parl, eval_sortB n, hs]; rfl

theorem eval_sortOE (hd : ∀ v, d.eval v = v) : ∀ n, (sortOE r d n).eval = Vec.sortOE r.eval n
  | 0 => rfl
  | n + 1 => by
      funext v
      change (mergeOE r d (n + 1)).eval ((two (sortOE r d n)).eval v) = _
      rw [eval_mergeOE hd, eval_two, eval_sortOE hd n]; rfl

theorem eval_sortV (n : Nat) : (sortV r n).eval = Vec.sortV r.eval n := by
  rw [sortV, eval_hrep, eval_vfly]; rfl

theorem eval_sortQ (hd : ∀ v, d.eval v = v) (n : Nat) : (sortQ r d n).eval = Vec.sortQ r.eval n := by
  rw [sortQ, eval_hrep, eval_qfly hd]; rfl

end Circuit

end Ruby
