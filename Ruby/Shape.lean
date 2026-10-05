import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Wire shapes

A Ruby circuit relates structured bundles of wires. A `Shape` describes such a
bundle: a single wire, a pair of bundles, or a vector of `n` bundles of the
same shape.

`Shape.Val β s` is the type of bundles of shape `s` whose individual wires carry
values of type `β`. Choosing `β` selects an interpretation of a circuit:

* `β = Bool` gives combinational (single-cycle) values,
* `β = Stream` (`Nat → Bool`) gives synchronous stream values,
* `β = Net` gives netlist signals used to emit SystemVerilog.

Vectors are functions out of `Fin n`, so vector equality is pointwise and
needs no length bookkeeping.
-/

namespace Ruby

inductive Shape where
  | bit
  | pair (a b : Shape)
  | vec (n : Nat) (a : Shape)
  deriving Repr, DecidableEq, Inhabited

namespace Shape

/-- Bundles of shape `s` whose wires carry values of type `β`. -/
@[reducible] def Val (β : Type) : Shape → Type
  | bit => β
  | pair a b => Val β a × Val β b
  | vec n a => Fin n → Val β a

/-- Apply `f` to every wire of a bundle. -/
def map {β γ : Type} (f : β → γ) : (s : Shape) → s.Val β → s.Val γ
  | bit, x => f x
  | pair a b, x => (map f a x.1, map f b x.2)
  | vec _ a, x => fun i => map f a (x i)

@[simp] theorem map_bit {β γ : Type} (f : β → γ) (x : β) : map f bit x = f x := rfl

@[simp] theorem map_pair {β γ : Type} (f : β → γ) (a b : Shape) (x : (pair a b).Val β) :
    map f (pair a b) x = (map f a x.1, map f b x.2) := rfl

@[simp] theorem map_vec {β γ : Type} (f : β → γ) (n : Nat) (a : Shape)
    (x : (vec n a).Val β) : map f (vec n a) x = fun i => map f a (x i) := rfl

theorem map_id {β : Type} : (s : Shape) → (x : s.Val β) → map id s x = x
  | bit, _ => rfl
  | pair a b, x => by simp [map_id a, map_id b]
  | vec _ a, x => by funext i; simp [map_id a]

theorem map_map {β γ δ : Type} (f : β → γ) (g : γ → δ) :
    (s : Shape) → (x : s.Val β) → map g s (map f s x) = map (g ∘ f) s x
  | bit, _ => rfl
  | pair a b, x => by simp [map_map f g a, map_map f g b]
  | vec _ a, x => by funext i; simp [map_map f g a]

/-- The number of wires in a bundle. -/
def width : Shape → Nat
  | bit => 1
  | pair a b => a.width + b.width
  | vec n a => n * a.width

end Shape

/-- A synchronous stream of bits: the value of a wire at each clock cycle. -/
abbrev Stream := Nat → Bool

namespace Shape

/-- The bundle of wire values present at clock cycle `t`. -/
def sample {s : Shape} (x : s.Val Stream) (t : Nat) : s.Val Bool :=
  map (fun w => w t) s x

/-- Turn a time-indexed family of bundles into a bundle of streams. -/
def unsample : (s : Shape) → (Nat → s.Val Bool) → s.Val Stream
  | bit, g => g
  | pair a b, g => (unsample a fun t => (g t).1, unsample b fun t => (g t).2)
  | vec _ a, g => fun i => unsample a fun t => g t i

@[simp] theorem sample_unsample : (s : Shape) → (g : Nat → s.Val Bool) → (t : Nat) →
    sample (unsample s g) t = g t
  | bit, _, _ => rfl
  | pair a b, g, t => by
      simp only [sample, unsample, map_pair]
      exact Prod.ext (sample_unsample a _ t) (sample_unsample b _ t)
  | vec _ a, g, t => by
      funext i
      exact sample_unsample a (fun t => g t i) t

@[simp] theorem sample_pair {a b : Shape} (x : (pair a b).Val Stream) (t : Nat) :
    sample x t = (sample x.1 t, sample x.2 t) := rfl

@[simp] theorem sample_vec {n : Nat} {a : Shape} (x : (vec n a).Val Stream) (t : Nat) :
    sample x t = fun i => sample (x i) t := rfl

@[simp] theorem sample_bit (x : bit.Val Stream) (t : Nat) : sample x t = x t := rfl

end Shape

/-- Words of `w` bits, least significant bit at index `0`. -/
abbrev Shape.word (w : Nat) : Shape := .vec w .bit

end Ruby
