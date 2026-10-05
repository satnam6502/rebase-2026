import Ruby.Sorter.Cell
import Ruby.Sorting

/-!
# The two-sorter cell is a comparator

Words are unsigned, least significant bit first (`wordVal`). The CARRY4 chain
computes `a ≥ b` (`eval_geC`): a carry chain adding `a + ~b + c₀` carries out
exactly when `b < a + c₀` (`carryChain_ge`), and a column of `k` CARRY4 slices
is one carry chain over `4 k` bits (`col_geTile`). The two halves then select
the minimum and the maximum, so the cell commutes with `wordVal` and the
comparator `cmp` (`twoSorter_commutes`).
-/

namespace Ruby.Sorter

open Shape Circuit Vec

/-! ## Carry chains -/

/-- The value of the low `n` bits of a bit sequence, least significant first. -/
def bitsVal (a : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bitsVal a n + (a n).toNat * 2 ^ n

theorem bitsVal_lt (a : Nat → Bool) : ∀ n, bitsVal a n < 2 ^ n
  | 0 => by simp [bitsVal]
  | n + 1 => by
      have := bitsVal_lt a n
      simp only [bitsVal, Nat.pow_succ]
      cases a n <;> simp <;> omega

/-- One bit of the comparator's carry chain. -/
theorem carry_step (x y c : Bool) (A B P : Nat) (hA : A < P) (hB : B < P) :
    (if (x == y) = true then decide (B < A + c.toNat) else x) =
      decide (B + y.toNat * P < A + x.toNat * P + c.toNat) := by
  cases x <;> cases y <;> cases c <;> simp <;> omega

/-- **A carry chain adding `a + ~b + c₀` carries out exactly when `b < a + c₀`.**
With `S = a XNOR b` and `DI = a` this is the CARRY4 comparator. -/
theorem carryChain_ge (a b : Nat → Bool) (c₀ : Bool) : ∀ n,
    carryChain c₀ (fun i => a i == b i) a n = decide (bitsVal b n < bitsVal a n + c₀.toNat)
  | 0 => by cases c₀ <;> simp [carryChain, bitsVal]
  | n + 1 => by
      have ih := carryChain_ge a b c₀ n
      have ha := bitsVal_lt a n
      have hb := bitsVal_lt b n
      simp only [carryChain, bitsVal, ih]
      exact carry_step _ _ _ _ _ _ ha hb

theorem carryChain_congr {c : Bool} {s s' di di' : Nat → Bool} :
    ∀ n, (∀ i < n, s i = s' i) → (∀ i < n, di i = di' i) →
      carryChain c s di n = carryChain c s' di' n
  | 0, _, _ => rfl
  | n + 1, hs, hd => by
      simp only [carryChain, hs n (by omega), hd n (by omega),
        carryChain_congr n (fun i hi => hs i (by omega)) (fun i hi => hd i (by omega))]

/-- A carry chain resumed after `m` bits. -/
theorem carryChain_shift (c : Bool) (s di : Nat → Bool) (m : Nat) : ∀ n,
    carryChain (carryChain c s di m) (fun i => s (m + i)) (fun i => di (m + i)) n =
      carryChain c s di (m + n)
  | 0 => rfl
  | n + 1 => by simp only [carryChain, carryChain_shift c s di m n]; rfl

/-! ## The comparator -/

/-- The unsigned value of a word. -/
def wordVal {w : Nat} (v : Fin w → Bool) : Nat :=
  bitsVal (fun i => if h : i < w then v ⟨i, h⟩ else false) w

/-- The bits of a sequence of chunks, concatenated. -/
def catBits {k : Nat} (xs : Fin k → Fin 4 → Bool) (i : Nat) : Bool :=
  if h : i < k * 4 then xs ⟨i / 4, by omega⟩ ⟨i % 4, by omega⟩ else false

theorem geTile_carry (c : CarryState.Val Bool) (x : Chunk.Val Bool) :
    (geTile.eval (c, x)).2 =
      (carryChain (c.1 || c.2) (get4 fun i => x.1 i == x.2 i) (get4 x.1) 4, false) := by
  rfl

/-- **A column of `k` CARRY4 slices is one carry chain over `4 k` bits.** -/
theorem col_geTile : ∀ (k : Nat) (c : CarryState.Val Bool) (xs : Fin k → Chunk.Val Bool),
    (((col k geTile).eval (c, xs)).2.1 || ((col k geTile).eval (c, xs)).2.2) =
      carryChain (c.1 || c.2)
        (fun i => catBits (fun j => (xs j).1) i == catBits (fun j => (xs j).2) i)
        (catBits fun j => (xs j).1) (k * 4)
  | 0, c, xs => rfl
  | k + 1, c, xs => by
      have ih := col_geTile k (geTile.eval (c, xs 0)).2 (fun j => xs j.succ)
      have hstep : ((col (k + 1) geTile).eval (c, xs)).2 =
          ((col k geTile).eval ((geTile.eval (c, xs 0)).2, fun j => xs j.succ)).2 := rfl
      rw [hstep, ih, geTile_carry]
      simp only [Bool.or_false]
      rw [show (k + 1) * 4 = 4 + k * 4 by omega, ← carryChain_shift]
      congr 1
      · apply carryChain_congr 4
        · intro i hi
          have e1 : (⟨i / 4, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp; omega)
          have e2 : (⟨i % 4, by omega⟩ : Fin 4) = ⟨i, hi⟩ := Fin.ext (by simp; omega)
          simp only [get4, hi, ↓reduceDIte, catBits, show i < (k + 1) * 4 by omega, e1, e2]
        · intro i hi
          have e1 : (⟨i / 4, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp; omega)
          have e2 : (⟨i % 4, by omega⟩ : Fin 4) = ⟨i, hi⟩ := Fin.ext (by simp; omega)
          simp only [get4, hi, ↓reduceDIte, catBits, show i < (k + 1) * 4 by omega, e1, e2]
      · funext i
        simp only [catBits]
        by_cases hi : i < k * 4
        · simp only [hi, ↓reduceDIte, show 4 + i < (k + 1) * 4 by omega]
          have e1 : (⟨(4 + i) / 4, by omega⟩ : Fin (k + 1)) = (⟨i / 4, by omega⟩ : Fin k).succ :=
            Fin.ext (by simp)
          have e2 : (⟨(4 + i) % 4, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp)
          rw [e1, e2]
        · simp only [hi, ↓reduceDIte, show ¬ 4 + i < (k + 1) * 4 by omega]
      · funext i
        simp only [catBits]
        by_cases hi : i < k * 4
        · simp only [hi, ↓reduceDIte, show 4 + i < (k + 1) * 4 by omega]
          have e1 : (⟨(4 + i) / 4, by omega⟩ : Fin (k + 1)) = (⟨i / 4, by omega⟩ : Fin k).succ :=
            Fin.ext (by simp)
          have e2 : (⟨(4 + i) % 4, by omega⟩ : Fin 4) = ⟨i % 4, by omega⟩ := Fin.ext (by simp)
          rw [e1, e2]
        · simp only [hi, ↓reduceDIte, show ¬ 4 + i < (k + 1) * 4 by omega]

theorem catBits_chunk {k : Nat} (v : Fin (k * 4) → Bool) :
    catBits (fun j => chunk v j) = fun i => if h : i < k * 4 then v ⟨i, h⟩ else false := by
  funext i
  simp only [catBits, chunk]
  split_ifs
  · congr 1; apply Fin.ext; simp; omega
  · rfl

/-- After at least one slice the chain state has `CYINIT = 0`. -/
theorem col_geTile_cyinit : ∀ (k : Nat) (c : CarryState.Val Bool) (xs : Fin (k + 1) → Chunk.Val Bool),
    ((col (k + 1) geTile).eval (c, xs)).2.2 = false
  | 0, _, _ => rfl
  | k + 1, c, xs => col_geTile_cyinit k (geTile.eval (c, xs 0)).2 (fun j => xs j.succ)

/-- **The CARRY4 chain compares**: `geC k` computes `a ≥ b` on `4 k`-bit words. -/
theorem eval_geC {k : Nat} (hk : 0 < k) (a b : Fin (k * 4) → Bool) :
    (geC k).eval (a, b) = decide (wordVal b ≤ wordVal a) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := col_geTile (k + 1) (false, true) (fun j => (chunk a j, chunk b j))
  have hcy := col_geTile_cyinit k (false, true) (fun j => (chunk a j, chunk b j))
  rw [hcy, Bool.or_false] at h
  simp only [Bool.false_or, catBits_chunk] at h
  change ((col (k + 1) geTile).eval ((false, true), fun j => (chunk a j, chunk b j))).2.1 = _
  rw [h, carryChain_ge]
  simp only [wordVal, Bool.toNat_true]
  apply decide_eq_decide.mpr
  omega

/-! ## The cell -/

theorem eval_muxReg (w : Nat) (s : Bool) (a b : Fin w → Bool) :
    (muxReg w).eval (s, (a, b)) = if s then b else a := by
  funext i
  cases s <;> rfl

theorem eval_halfMin {k : Nat} (hk : 0 < k) (a b : Fin (k * 4) → Bool) :
    (halfMin k).eval (a, b) = if wordVal b ≤ wordVal a then b else a := by
  change (muxReg (k * 4)).eval ((geC k).eval (a, b), (a, b)) = _
  rw [eval_muxReg, eval_geC hk]
  by_cases h : wordVal b ≤ wordVal a <;> simp [h]

theorem eval_halfMax {k : Nat} (hk : 0 < k) (a b : Fin (k * 4) → Bool) :
    (halfMax k).eval (a, b) = if wordVal a ≤ wordVal b then b else a := by
  change (muxReg (k * 4)).eval ((geC k).eval (b, a), (a, b)) = _
  rw [eval_muxReg, eval_geC hk]
  by_cases h : wordVal a ≤ wordVal b <;> simp [h]

/-- **The two-sorter cell commutes with decoding**: decoded, it is the
comparator. -/
theorem twoSorter_commutes {k : Nat} (hk : 0 < k) :
    Commutes wordVal (twoSorter k).eval cmp := by
  intro v
  funext j
  have hv0 := eval_halfMin hk (v 0) (v 1)
  have hv1 := eval_halfMax hk (v 0) (v 1)
  rcases fin2_cases j with rfl | rfl
  · change wordVal ((halfMin k).eval (v 0, v 1)) = min (wordVal (v 0)) (wordVal (v 1))
    rw [hv0]
    by_cases h : wordVal (v 1) ≤ wordVal (v 0)
    · simp [h]
    · simp [h, min_eq_left (le_of_lt (not_le.mp h))]
  · change wordVal ((halfMax k).eval (v 0, v 1)) = max (wordVal (v 0)) (wordVal (v 1))
    rw [hv1]
    by_cases h : wordVal (v 0) ≤ wordVal (v 1)
    · simp [h]
    · simp [h, max_eq_left (le_of_lt (not_le.mp h))]

theorem eval_delayW (w : Nat) (v : Fin w → Bool) : (delayW w).eval v = v := rfl

end Ruby.Sorter
