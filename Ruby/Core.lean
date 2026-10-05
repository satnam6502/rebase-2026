import Ruby.Shape

/-!
# Ruby circuits

A circuit is a term of the inductive type `Circuit a b`, relating bundles of
shape `a` to bundles of shape `b`. The constructors are the Ruby combinators:

* `prim p`: a primitive cell (a Xilinx 7-series LUT, CARRY4 or FDCE),
* `wire w`: pure wiring, which builds no hardware,
* `seq d r s`: serial composition `r ; s`; `d` says where `s` is placed
  relative to `r` (to the right, above, or on top of it),
* `par r s`: parallel composition `[r, s]` on pairs; `r` is placed below `s`,
* `map n r`: `n` copies of `r` on a vector, stacked bottom to top.

Because circuits are data, every interpretation is a structural recursion:
behaviour (`Circuit.eval`, `Circuit.evalS`), latency, layout and netlists.

Wiring is a function that is polymorphic in the type of a wire, so it can only
route, copy, drop or tie off wires. Its single obligation, `natural`, records
that it commutes with any change of wire type; it is discharged by `rfl` for
all wiring in this library.
-/

namespace Ruby

open Shape

variable {a b c d : Shape}

/-- Pure wiring from shape `a` to shape `b`. `run k x` may use `k` to tie a
wire to a constant. -/
structure Wiring (a b : Shape) where
  run : {β : Type} → (Bool → β) → a.Val β → b.Val β
  natural : ∀ {β γ : Type} (f : β → γ) (k : Bool → β) (x : a.Val β),
    b.map f (run k x) = run (f ∘ k) (a.map f x) := by intros; rfl

/-! ## Xilinx 7-series primitives -/

/-- CARRY4 inputs `((CI, CYINIT), (DI, S))`. -/
abbrev Carry4In : Shape := .pair (.pair .bit .bit) (.pair (.word 4) (.word 4))

/-- CARRY4 outputs `(O, CO)`. -/
abbrev Carry4Out : Shape := .pair (.word 4) (.word 4)

/-- Primitive cells. `lut k f` is a `k`-input LUT computing `f`, where input
`i` of the vector is pin `I{i}`. -/
inductive Prim : Shape → Shape → Type where
  | lut (k : Nat) (f : (Fin k → Bool) → Bool) : Prim (.word k) .bit
  | carry4 : Prim Carry4In Carry4Out
  | fdce : Prim .bit .bit

/-- The carry into bit `i` of a CARRY4 chain whose carry into bit `0` is `c0`:
`CO[i] = S[i] ? carry-in : DI[i]`. -/
def carryChain (c0 : Bool) (s di : Nat → Bool) : Nat → Bool
  | 0 => c0
  | i + 1 => if s i then carryChain c0 s di i else di i

/-- Extend a 4-bit vector to all indices, reading `false` beyond bit 3. -/
def get4 (v : Fin 4 → Bool) (i : Nat) : Bool :=
  if h : i < 4 then v ⟨i, h⟩ else false

/-- The UNISIM `CARRY4` model: `O = S ^ {CO[2:0], CI | CYINIT}` and
`CO = (S & {CO[2:0], CI | CYINIT}) | (~S & DI)`. -/
def carry4Fn (x : Carry4In.Val Bool) : Carry4Out.Val Bool :=
  let c0 := x.1.1 || x.1.2
  let c := carryChain c0 (get4 x.2.2) (get4 x.2.1)
  (fun i => xor (x.2.2 i) (c i.val), fun i => c (i.val + 1))

namespace Prim

/-- Clock cycles from input to output: `1` for a register, `0` otherwise. -/
def latency : Prim a b → Nat
  | lut .. => 0
  | carry4 => 0
  | fdce => 1

/-- The value computed by a primitive in one clock cycle. A register passes its
input through; its delay is accounted for by `latency`. -/
def eval : Prim a b → a.Val Bool → b.Val Bool
  | lut _ f, x => f x
  | carry4, x => carry4Fn x
  | fdce, x => x

/-- A register that clears to `0` on reset and loads `D` on every clock edge. -/
def delay (x : Stream) : Stream
  | 0 => false
  | t + 1 => x t

/-- Synchronous stream semantics: combinational cells act at each cycle, and an
`FDCE` delays its input by one cycle. -/
def evalS : Prim a b → a.Val Stream → b.Val Stream
  | fdce, x => delay x
  | p, x => unsample b fun t => p.eval (sample x t)

end Prim

/-! ## Circuits -/

/-- Where the second circuit of a serial composition is placed. -/
inductive Dir where
  | beside
  | below
  | overlay
  deriving Repr, DecidableEq

inductive Circuit : Shape → Shape → Type 1 where
  | prim {a b : Shape} (p : Prim a b) : Circuit a b
  | wire {a b : Shape} (w : Wiring a b) : Circuit a b
  | seq {a b c : Shape} (d : Dir) (r : Circuit a b) (s : Circuit b c) : Circuit a c
  | par {a b c d : Shape} (r : Circuit a b) (s : Circuit c d) :
      Circuit (.pair a c) (.pair b d)
  | map {a b : Shape} (n : Nat) (r : Circuit a b) : Circuit (.vec n a) (.vec n b)

namespace Circuit

/-- Serial composition, `s` to the right of `r`. -/
infixr:60 " >-> " => Circuit.seq Dir.beside
/-- Serial composition, `s` above `r`. -/
infixr:60 " >^> " => Circuit.seq Dir.below
/-- Serial composition, `s` on top of `r` (sharing the same sites, e.g. a LUT
and the flip-flop it drives). -/
infixr:60 " >|> " => Circuit.seq Dir.overlay
/-- Parallel composition on a pair, `r` below `s`. -/
infixr:65 " ‖ " => Circuit.par

/-- Combinational semantics: the value of each output for one clock cycle. -/
def eval : {a b : Shape} → Circuit a b → a.Val Bool → b.Val Bool
  | _, _, prim p, x => p.eval x
  | _, _, wire w, x => w.run id x
  | _, _, seq _ r s, x => s.eval (r.eval x)
  | _, _, par r s, x => (r.eval x.1, s.eval x.2)
  | _, _, map _ r, x => fun i => r.eval (x i)

/-- Synchronous stream semantics. -/
def evalS : {a b : Shape} → Circuit a b → a.Val Stream → b.Val Stream
  | _, _, prim p, x => p.evalS x
  | _, _, wire w, x => w.run (fun b _ => b) x
  | _, _, seq _ r s, x => s.evalS (r.evalS x)
  | _, _, par r s, x => (r.evalS x.1, s.evalS x.2)
  | _, _, map _ r, x => fun i => r.evalS (x i)

/-- The number of registers on every path from input to output, if all paths
agree. -/
def latency : {a b : Shape} → Circuit a b → Option Nat
  | _, _, prim p => some p.latency
  | _, _, wire _ => some 0
  | _, _, seq _ r s =>
      match r.latency, s.latency with
      | some k, some l => some (k + l)
      | _, _ => none
  | _, _, par r s =>
      match r.latency, s.latency with
      | some k, some l => if k = l then some k else none
      | _, _ => none
  | _, _, map _ r => r.latency

@[simp] theorem eval_prim (p : Prim a b) (x : a.Val Bool) : (prim p).eval x = p.eval x := rfl
@[simp] theorem eval_wire (w : Wiring a b) (x : a.Val Bool) : (wire w).eval x = w.run id x := rfl
@[simp] theorem eval_seq (d : Dir) (r : Circuit a b) (s : Circuit b c) (x : a.Val Bool) :
    (seq d r s).eval x = s.eval (r.eval x) := rfl
@[simp] theorem eval_par (r : Circuit a b) (s : Circuit c d) (x : (Shape.pair a c).Val Bool) :
    (par r s).eval x = (r.eval x.1, s.eval x.2) := rfl
@[simp] theorem eval_map (n : Nat) (r : Circuit a b) (x : (Shape.vec n a).Val Bool) :
    (map n r).eval x = fun i => r.eval (x i) := rfl

/-! ## Retiming: streams agree with the combinational semantics -/

theorem Prim.evalS_sample (p : Prim a b) (x : a.Val Stream) (t : Nat) :
    sample (p.evalS x) (t + p.latency) = p.eval (sample x t) := by
  cases p with
  | fdce => rfl
  | lut k f => exact sample_unsample _ _ t
  | carry4 => exact sample_unsample _ _ t

/-- A circuit whose paths all carry `k` registers computes its combinational
function with a delay of exactly `k` cycles: the outputs at cycle `t + k` are
the combinational function of the inputs at cycle `t`. -/
theorem evalS_sample : {a b : Shape} → (c : Circuit a b) → (k : Nat) → c.latency = some k →
    ∀ (x : a.Val Stream) (t : Nat), sample (c.evalS x) (t + k) = c.eval (sample x t)
  | _, _, prim p, k, h, x, t => by
      simp only [latency, Option.some.injEq] at h
      subst h
      exact Prim.evalS_sample p x t
  | _, _, wire w, k, h, x, t => by
      simp only [latency, Option.some.injEq] at h
      subst h
      exact w.natural (fun s => s t) (fun b _ => b) x
  | _, _, seq _ r s, k, h, x, t => by
      cases hr : r.latency with
      | none => simp [latency, hr] at h
      | some kr =>
        cases hs : s.latency with
        | none => simp [latency, hr, hs] at h
        | some ks =>
          simp only [latency, hr, hs, Option.some.injEq] at h
          subst h
          simp only [evalS, eval, ← Nat.add_assoc]
          rw [evalS_sample s ks hs, evalS_sample r kr hr]
  | _, _, par r s, k, h, x, t => by
      cases hr : r.latency with
      | none => simp [latency, hr] at h
      | some kr =>
        cases hs : s.latency with
        | none => simp [latency, hr, hs] at h
        | some ks =>
          by_cases hk : kr = ks
          · subst hk
            simp only [latency, hr, hs, ↓reduceIte, Option.some.injEq] at h
            subst h
            simp only [evalS, eval, sample_pair]
            rw [evalS_sample r kr hr, evalS_sample s kr hs]
          · simp [latency, hr, hs, hk] at h
  | _, _, map _ r, k, h, x, t => by
      simp only [latency] at h
      funext i
      simp only [evalS, eval, sample_vec]
      exact evalS_sample r k h (x i) t

end Circuit

end Ruby
