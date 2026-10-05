import Mathlib.Data.Fin.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Vector networks

Functions on vectors `Fin n → α`, the values that flow through the vector
combinators of a Ruby circuit. Each Ruby wiring combinator has its value-level
counterpart here, and the circuit combinators in `Ruby.Combinators` are defined
so that their combinational semantics *is* the function defined here
(definitionally).

The connection patterns follow Sheeran's butterflies and the Lava sorter
cores: halves (`lo`, `hi`, `append`), `riffle` and `unriffle`, `two`, `ilv`,
`evens`, `midEvens`, `alt`, `vee` and `que`.

Lengths are written `m * 2`, so a vector of `2 ^ (n + 1)` elements is
definitionally one of `2 ^ n * 2` elements and recursive networks need no
casts.
-/

namespace Ruby.Vec

/-- Close the index arithmetic left after unfolding wiring: split every
conditional, clean up the `False ∨ _` hypotheses that splitting leaves, and
call `omega`. -/
macro "fin_omega" : tactic =>
  `(tactic| (split_ifs <;> (try simp only [false_or, or_false, false_and, and_false] at *) <;> omega))

/-- Close an equation between two wires selected by index arithmetic. -/
macro "idx_eq" : tactic =>
  `(tactic| first | omega | rfl | (congr 1; done) | (congr 1; apply Fin.ext; simp only; omega))

variable {α β : Type}

/-- A network on `n` wires. -/
abbrev Net (α : Type) (n : Nat) := (Fin n → α) → (Fin n → α)

/-- Serial composition of networks, left to right. -/
def seq {n : Nat} (f g : Net α n) : Net α n := fun x => g (f x)

@[inherit_doc] scoped infixl:60 " ⨾ " => Ruby.Vec.seq

@[simp] theorem seq_apply {n : Nat} (f g : Net α n) (x : Fin n → α) : (f ⨾ g) x = g (f x) := rfl

theorem seq_assoc {n : Nat} (f g h : Net α n) : (f ⨾ g) ⨾ h = f ⨾ (g ⨾ h) := rfl

/-! ## Halves -/

/-- The first half. -/
def lo {m : Nat} (x : Fin (m * 2) → α) : Fin m → α := fun i => x ⟨i, by omega⟩

/-- The second half. -/
def hi {m : Nat} (x : Fin (m * 2) → α) : Fin m → α := fun i => x ⟨m + i, by omega⟩

/-- Concatenation of two halves. -/
def append {m : Nat} (u v : Fin m → α) : Fin (m * 2) → α := fun j =>
  if h : j.val < m then u ⟨j, h⟩ else v ⟨j - m, by omega⟩

@[simp] theorem lo_apply {m : Nat} (x : Fin (m * 2) → α) (i : Fin m) :
    lo x i = x ⟨i, by omega⟩ := rfl

@[simp] theorem hi_apply {m : Nat} (x : Fin (m * 2) → α) (i : Fin m) :
    hi x i = x ⟨m + i, by omega⟩ := rfl

theorem append_apply {m : Nat} (u v : Fin m → α) (j : Fin (m * 2)) :
    append u v j = if h : j.val < m then u ⟨j, h⟩ else v ⟨j - m, by omega⟩ := rfl

@[simp] theorem lo_append {m : Nat} (u v : Fin m → α) : lo (append u v) = u := by
  funext i; simp [append]

@[simp] theorem hi_append {m : Nat} (u v : Fin m → α) : hi (append u v) = v := by
  funext i
  simp only [hi_apply, append, show ¬(m + i.val < m) by omega, ↓reduceDIte]
  congr 1; ext; simp

@[simp] theorem append_lo_hi {m : Nat} (x : Fin (m * 2) → α) : append (lo x) (hi x) = x := by
  funext j
  by_cases h : j.val < m
  · simp [append, h]
  · simp only [append, h, dite_false, hi_apply]
    congr 1; ext; simp; omega

/-- `parl f g` applies `f` to the first half and `g` to the second. -/
def parl {m : Nat} (f g : Net α m) : Net α (m * 2) := fun x => append (f (lo x)) (g (hi x))

/-- Two copies of `f`, one on each half. -/
def two {m : Nat} (f : Net α m) : Net α (m * 2) := parl f f

@[simp] theorem parl_append {m : Nat} (f g : Net α m) (u v : Fin m → α) :
    parl f g (append u v) = append (f u) (g v) := by simp [parl]

@[simp] theorem two_append {m : Nat} (f : Net α m) (u v : Fin m → α) :
    two f (append u v) = append (f u) (f v) := by simp [two]

/-! ## Riffles -/

/-- The wires at even positions. -/
def evensIdx {m : Nat} (x : Fin (m * 2) → α) : Fin m → α := fun i => x ⟨2 * i, by omega⟩

/-- The wires at odd positions. -/
def oddsIdx {m : Nat} (x : Fin (m * 2) → α) : Fin m → α := fun i => x ⟨2 * i + 1, by omega⟩

/-- Two vectors, alternately. -/
def interleave {m : Nat} (u v : Fin m → α) : Fin (m * 2) → α := fun j =>
  if j.val % 2 = 0 then u ⟨j / 2, by omega⟩ else v ⟨j / 2, by omega⟩

/-- Unshuffle: the even positions, then the odd ones. -/
def unriffle {m : Nat} : Net α (m * 2) := fun x => append (evensIdx x) (oddsIdx x)

/-- The perfect shuffle: interleave the two halves. -/
def riffle {m : Nat} : Net α (m * 2) := fun x => interleave (lo x) (hi x)

@[simp] theorem evensIdx_apply {m : Nat} (x : Fin (m * 2) → α) (i : Fin m) :
    evensIdx x i = x ⟨2 * i, by omega⟩ := rfl

@[simp] theorem oddsIdx_apply {m : Nat} (x : Fin (m * 2) → α) (i : Fin m) :
    oddsIdx x i = x ⟨2 * i + 1, by omega⟩ := rfl

@[simp] theorem evensIdx_interleave {m : Nat} (u v : Fin m → α) :
    evensIdx (interleave u v) = u := by
  funext i
  simp only [evensIdx, interleave, Nat.mul_mod_right, ↓reduceIte]
  congr 1; ext; simp

@[simp] theorem oddsIdx_interleave {m : Nat} (u v : Fin m → α) :
    oddsIdx (interleave u v) = v := by
  funext i
  have h : (2 * i.val + 1) % 2 ≠ 0 := by omega
  simp only [oddsIdx, interleave, h, ↓reduceIte]
  congr 1; ext; simp; omega

@[simp] theorem interleave_evensIdx_oddsIdx {m : Nat} (x : Fin (m * 2) → α) :
    interleave (evensIdx x) (oddsIdx x) = x := by
  funext j
  simp only [interleave, evensIdx, oddsIdx]
  split_ifs with h <;> congr 1 <;> ext <;> simp <;> omega

@[simp] theorem riffle_unriffle {m : Nat} (x : Fin (m * 2) → α) : riffle (unriffle x) = x := by
  simp [riffle, unriffle]

@[simp] theorem unriffle_riffle {m : Nat} (x : Fin (m * 2) → α) : unriffle (riffle x) = x := by
  simp [riffle, unriffle]

@[simp] theorem riffle_append {m : Nat} (u v : Fin m → α) : riffle (append u v) = interleave u v := by
  simp [riffle]

@[simp] theorem unriffle_interleave {m : Nat} (u v : Fin m → α) :
    unriffle (interleave u v) = append u v := by
  simp [unriffle]

/-- `ilv f` applies `f` to the even positions and to the odd positions. -/
def ilv {m : Nat} (f : Net α m) : Net α (m * 2) := unriffle ⨾ two f ⨾ riffle

theorem ilv_apply {m : Nat} (f : Net α m) (x : Fin (m * 2) → α) :
    ilv f x = interleave (f (evensIdx x)) (f (oddsIdx x)) := by
  simp [ilv, unriffle]

@[simp] theorem ilv_interleave {m : Nat} (f : Net α m) (u v : Fin m → α) :
    ilv f (interleave u v) = interleave (f u) (f v) := by
  simp [ilv_apply]

/-! ## Columns of two-input cells -/

/-- The adjacent pairs `(2 i, 2 i + 1)`. -/
def pairs {m : Nat} (x : Fin (m * 2) → α) : Fin m → Fin 2 → α :=
  fun i j => x ⟨2 * i + j, by omega⟩

/-- Flatten pairs. -/
def unpairs {m : Nat} (y : Fin m → Fin 2 → α) : Fin (m * 2) → α :=
  fun j => y ⟨j / 2, by omega⟩ ⟨j % 2, by omega⟩

/-- `evens f` applies the two-input cell `f` to each adjacent pair. -/
def evens {m : Nat} (f : Net α 2) : Net α (m * 2) := fun x => unpairs fun i => f (pairs x i)

@[simp] theorem pairs_unpairs {m : Nat} (y : Fin m → Fin 2 → α) : pairs (unpairs y) = y := by
  funext i j
  simp only [pairs, unpairs]
  congr 1 <;> (ext; simp; try omega)

@[simp] theorem unpairs_pairs {m : Nat} (x : Fin (m * 2) → α) : unpairs (pairs x) = x := by
  funext j
  simp only [pairs, unpairs]
  congr 1; ext; simp; omega

theorem evens_apply {m : Nat} (f : Net α 2) (x : Fin (m * 2) → α) (j : Fin (m * 2)) :
    evens f x j = f (fun b => x ⟨2 * (j / 2) + b, by omega⟩) ⟨j % 2, by omega⟩ := rfl

/-- The pair `(2 i + 1, 2 i + 2)` that the middle wire `j` belongs to, where
`i = (j - 1) / 2`. Indices are clamped so the function is total; the clamp is
inactive on middle wires. -/
def midPair {m : Nat} (x : Fin (m * 2) → α) (j : Fin (m * 2)) : Fin 2 → α := fun b =>
  x ⟨if 2 * ((j.val - 1) / 2) + 1 + b.val < m * 2 then 2 * ((j.val - 1) / 2) + 1 + b.val
      else m * 2 - 1, by have := j.isLt; split_ifs <;> omega⟩

theorem midPair_of_not_end {m : Nat} (x : Fin (m * 2) → α) (j : Fin (m * 2))
    (h : ¬ (j.val = 0 ∨ j.val = m * 2 - 1)) (b : Fin 2) :
    midPair x j b = x ⟨2 * ((j.val - 1) / 2) + 1 + b.val, by
      have := j.isLt; have := b.isLt; omega⟩ := by
  have := j.isLt; have := b.isLt
  simp only [midPair]
  congr 1; apply Fin.ext; simp only; split_ifs <;> omega

theorem midPair_eq_of_not_end {m : Nat} (x : Fin (m * 2) → α) (j : Fin (m * 2))
    (h : ¬ (j.val = 0 ∨ j.val = m * 2 - 1)) :
    midPair x j = fun b => x ⟨2 * ((j.val - 1) / 2) + 1 + b.val, by
      have := j.isLt; have := b.isLt; omega⟩ := by
  funext b; exact midPair_of_not_end x j h b

/-- Is `j` the first or the last wire? -/
def IsEnd {m : Nat} (j : Fin (m * 2)) : Prop := j.val = 0 ∨ j.val = m * 2 - 1

instance {m : Nat} (j : Fin (m * 2)) : Decidable (IsEnd j) := by unfold IsEnd; infer_instance

/-- `midEvens f` passes the first and last wires through and applies `f` to the
pairs `(2 i + 1, 2 i + 2)` in between: the last column of Batcher's odd–even
merger. -/
def midEvens {m : Nat} (f : Net α 2) : Net α (m * 2) := fun x j =>
  if IsEnd j then x j else f (midPair x j) ⟨(j.val - 1) % 2, by omega⟩

/-! ## The patterns of the periodic mergers -/

/-- The index map of `alt`: swap the pairs at odd pair positions. -/
def altIdx {m : Nat} (j : Fin (m * 2)) : Fin (m * 2) :=
  if (j.val / 2) % 2 = 1 then
    if h : j.val % 2 = 0 then ⟨j + 1, by have := j.isLt; omega⟩ else ⟨j - 1, by omega⟩
  else j

/-- `alt` swaps every second pair: `[0, 1, 3, 2, 4, 5, 7, 6, …]`. -/
def alt {m : Nat} : Net α (m * 2) := fun x j => x (altIdx j)

/-- Reverse a vector. -/
def rev {n : Nat} : Net α n := fun x i => x ⟨n - 1 - i, by omega⟩

/-- Dowd et al.'s pattern: `ilv` between two `alt`s. -/
def vee {m : Nat} (f : Net α m) : Net α (m * 2) := alt ⨾ ilv f ⨾ alt

/-- Canfield and Williamson's pattern: `two`, between interleaved shuffles. -/
def que {m : Nat} (f : Net α (m * 2)) : Net α (m * 2 * 2) :=
  ilv unriffle ⨾ two f ⨾ ilv riffle

/-- `k` copies of `f` in series. -/
def hrep {n : Nat} : Nat → Net α n → Net α n
  | 0, _ => id
  | k + 1, f => f ⨾ hrep k f

/-! ## Elementwise maps commute with wiring

A wiring only moves values, so it commutes with applying a function `g` to
every element. `Commutes g F F'` says the network `F` on `α` and `F'` on `β`
agree through `g`. -/

/-- `F` followed by `g` everywhere is `g` everywhere followed by `F'`. -/
def Commutes {n : Nat} (g : α → β) (F : Net α n) (F' : Net β n) : Prop :=
  ∀ x, g ∘ F x = F' (g ∘ x)

namespace Commutes

variable {g : α → β}

theorem seq {n : Nat} {F G : Net α n} {F' G' : Net β n}
    (hF : Commutes g F F') (hG : Commutes g G G') : Commutes g (F ⨾ G) (F' ⨾ G') := by
  intro x; simp [hG (F x), hF x]

theorem id' {n : Nat} : Commutes g (id : Net α n) id := fun _ => rfl

theorem parl {m : Nat} {F G : Net α m} {F' G' : Net β m}
    (hF : Commutes g F F') (hG : Commutes g G G') :
    Commutes g (Vec.parl F G) (Vec.parl F' G') := by
  intro x
  funext j
  have hl : g ∘ lo x = lo (g ∘ x) := rfl
  have hh : g ∘ hi x = hi (g ∘ x) := rfl
  simp only [Function.comp, Vec.parl, append]
  split_ifs
  · rw [← hl, ← hF]; rfl
  · rw [← hh, ← hG]; rfl

theorem two {m : Nat} {F : Net α m} {F' : Net β m} (hF : Commutes g F F') :
    Commutes g (Vec.two F) (Vec.two F') := parl hF hF

theorem unriffle {m : Nat} : Commutes g (Vec.unriffle : Net α (m * 2)) Vec.unriffle := by
  intro x; funext j; simp only [Function.comp, Vec.unriffle, append]; split_ifs <;> rfl

theorem riffle {m : Nat} : Commutes g (Vec.riffle : Net α (m * 2)) Vec.riffle := by
  intro x; funext j; simp only [Function.comp, Vec.riffle, interleave]; split_ifs <;> rfl

theorem ilv {m : Nat} {F : Net α m} {F' : Net β m} (hF : Commutes g F F') :
    Commutes g (Vec.ilv F) (Vec.ilv F') := (unriffle.seq hF.two).seq riffle

theorem evens {m : Nat} {f : Net α 2} {f' : Net β 2} (hf : Commutes g f f') :
    Commutes g (Vec.evens f : Net α (m * 2)) (Vec.evens f') := by
  intro x; funext j
  exact congrFun (hf _) _

theorem midEvens {m : Nat} {f : Net α 2} {f' : Net β 2} (hf : Commutes g f f') :
    Commutes g (Vec.midEvens f : Net α (m * 2)) (Vec.midEvens f') := by
  intro x; funext j
  simp only [Function.comp, Vec.midEvens]
  split_ifs
  · rfl
  · exact congrFun (hf (midPair x j)) _

theorem alt {m : Nat} : Commutes g (Vec.alt : Net α (m * 2)) Vec.alt := fun _ => rfl

theorem rev {n : Nat} : Commutes g (Vec.rev : Net α n) Vec.rev := fun _ => rfl

theorem vee {m : Nat} {F : Net α m} {F' : Net β m} (hF : Commutes g F F') :
    Commutes g (Vec.vee F) (Vec.vee F') := (alt.seq hF.ilv).seq alt

theorem que {m : Nat} {F : Net α (m * 2)} {F' : Net β (m * 2)} (hF : Commutes g F F') :
    Commutes g (Vec.que F) (Vec.que F') :=
  (unriffle.ilv.seq hF.two).seq riffle.ilv

theorem hrep {n : Nat} {F : Net α n} {F' : Net β n} (hF : Commutes g F F') :
    ∀ k, Commutes g (Vec.hrep k F) (Vec.hrep k F')
  | 0 => id'
  | k + 1 => hF.seq (hrep hF k)

end Commutes

end Ruby.Vec
