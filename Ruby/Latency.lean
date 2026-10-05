import Ruby.Combinators
import Mathlib.Tactic.Ring

/-!
# Latency of the combinators

`Circuit.latency c = some k` says every path through `c` carries exactly `k`
registers; by `Circuit.evalS_sample` such a circuit computes its combinational
function `k` cycles late. These lemmas compute the latency of the combinators
and of the four butterfly sorters over a cell of latency `L`.
-/

namespace Ruby.Circuit

open Shape

variable {a b c x y : Shape}

theorem latency_seq {d : Dir} {r : Circuit a b} {s : Circuit b c} {k l : Nat}
    (hr : r.latency = some k) (hs : s.latency = some l) : (seq d r s).latency = some (k + l) := by
  simp [latency, hr, hs]

theorem latency_par {r : Circuit a b} {s : Circuit x y} {k : Nat}
    (hr : r.latency = some k) (hs : s.latency = some k) : (r ‖ s).latency = some k := by
  simp [latency, hr, hs]

theorem latency_wire (w : Wiring a b) : (wire w).latency = some 0 := rfl

theorem latency_map {n : Nat} {r : Circuit a b} {k : Nat} (hr : r.latency = some k) :
    (map n r).latency = some k := hr

theorem latency_idC : (idC : Circuit a a).latency = some 0 := rfl

theorem latency_fst {r : Circuit a b} (hr : r.latency = some 0) :
    (fst (c := c) r).latency = some 0 := latency_par hr latency_idC

theorem latency_snd {r : Circuit b c} (hr : r.latency = some 0) :
    (snd (a := a) r).latency = some 0 := latency_par latency_idC hr

theorem latency_wire_seq {d : Dir} (w : Wiring a b) {s : Circuit b c} {k : Nat}
    (hs : s.latency = some k) : (seq d (wire w) s).latency = some k := by
  simpa using latency_seq (d := d) (latency_wire w) hs

theorem latency_seq_wire {d : Dir} {r : Circuit a b} (w : Wiring b c) {k : Nat}
    (hr : r.latency = some k) : (seq d r (wire w)).latency = some k := by
  simpa using latency_seq (d := d) hr (latency_wire w)

theorem latency_parl {m : Nat} {r s : Circuit (.vec m a) (.vec m a)} {k : Nat}
    (hr : r.latency = some k) (hs : s.latency = some k) : (parl r s).latency = some k :=
  latency_wire_seq _ (latency_seq_wire _ (latency_par hr hs))

theorem latency_two {m : Nat} {r : Circuit (.vec m a) (.vec m a)} {k : Nat}
    (hr : r.latency = some k) : (two r).latency = some k := latency_parl hr hr

theorem latency_ilv {m : Nat} {r : Circuit (.vec m a) (.vec m a)} {k : Nat}
    (hr : r.latency = some k) : (ilv r).latency = some k :=
  latency_wire_seq _ (latency_seq_wire _ (latency_two hr))

theorem latency_evens {m : Nat} {r : Circuit (.vec 2 a) (.vec 2 a)} {k : Nat}
    (hr : r.latency = some k) : (evens (m := m) r).latency = some k :=
  latency_wire_seq _ (latency_seq_wire _ (latency_map hr))

theorem latency_midEvens {m : Nat} (h : 0 < m) {r : Circuit (.vec 2 a) (.vec 2 a)} {d : Circuit a a}
    {k : Nat} (hr : r.latency = some k) (hd : d.latency = some k) :
    (midEvens h r d).latency = some k :=
  latency_wire_seq _ (latency_seq_wire _ (latency_par hd (latency_par (latency_map hr) hd)))

theorem latency_vee {m : Nat} {r : Circuit (.vec m a) (.vec m a)} {k : Nat}
    (hr : r.latency = some k) : (vee r).latency = some k :=
  latency_wire_seq _ (latency_seq_wire _ (latency_ilv hr))

theorem latency_que {m : Nat} {r : Circuit (.vec (m * 2) a) (.vec (m * 2) a)} {k : Nat}
    (hr : r.latency = some k) : (que r).latency = some k := by
  have h := latency_seq (d := .beside) (latency_ilv (r := unriffle (a := a) (m := m)) rfl)
    (latency_seq (d := .beside) (latency_two hr) (latency_ilv (r := riffle (a := a) (m := m)) rfl))
  exact h.trans (by simp)

theorem latency_hrep {r : Circuit a a} {k : Nat} (hr : r.latency = some k) :
    ∀ j, (hrep j r).latency = some (j * k)
  | 0 => by simp [hrep, latency_idC]
  | j + 1 => by
      rw [hrep, latency_seq hr (latency_hrep hr j)]
      congr 1; ring

theorem latency_col {n : Nat} {r : Circuit (.pair c x) (.pair y c)} (hr : r.latency = some 0) :
    (col n r).latency = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact latency_wire_seq _ (by
      simpa using latency_seq (d := .below) (latency_fst hr)
        (latency_wire_seq _ (latency_seq_wire _ (latency_snd ih))))

/-! ## The butterfly sorters -/

variable {r : Circuit (.vec 2 a) (.vec 2 a)} {d : Circuit a a} {L : Nat}

theorem latency_bfly (hr : r.latency = some L) : ∀ n, (bfly r n).latency = some (n * L)
  | 0 => by simp [bfly, latency_idC]
  | 1 => by simp [bfly, hr]
  | n + 2 => by
      exact (latency_seq (latency_ilv (latency_bfly hr (n + 1))) (latency_evens hr)).trans
        (by congr 1; ring)

theorem latency_mergeOE (hr : r.latency = some L) (hd : d.latency = some L) :
    ∀ n, (mergeOE r d n).latency = some (n * L)
  | 0 => by simp [mergeOE, latency_idC]
  | 1 => by simp [mergeOE, hr]
  | n + 2 => by
      exact (latency_seq (latency_ilv (latency_mergeOE hr hd (n + 1)))
        (latency_midEvens _ hr hd)).trans (by congr 1; ring)

theorem latency_vfly (hr : r.latency = some L) : ∀ n, (vfly r n).latency = some (n * L)
  | 0 => by simp [vfly, latency_idC]
  | 1 => by simp [vfly, hr]
  | n + 2 => by
      exact (latency_seq (latency_vee (latency_vfly hr (n + 1))) (latency_evens hr)).trans
        (by congr 1; ring)

theorem latency_qfly (hr : r.latency = some L) (hd : d.latency = some L) :
    ∀ n, (qfly r d n).latency = some (n * L)
  | 0 => by simp [qfly, latency_idC]
  | 1 => by simp [qfly, hr]
  | n + 2 => by
      exact (latency_seq (latency_que (m := 2 ^ n) (latency_qfly hr hd (n + 1)))
        (latency_midEvens _ hr hd)).trans (by congr 1; ring)

/-- The `n`-th triangular number, the number of stages of a recursive sorter. -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

theorem two_mul_tri : ∀ n, 2 * tri n = n * (n + 1)
  | 0 => rfl
  | n + 1 => by rw [tri, Nat.mul_add, two_mul_tri n]; ring

theorem latency_sortB (hr : r.latency = some L) : ∀ n, (sortB r n).latency = some (tri n * L)
  | 0 => by simp [sortB, tri, latency_idC]
  | n + 1 => by
      have hs := latency_sortB hr n
      exact (latency_seq (latency_parl hs (latency_seq_wire _ hs)) (latency_bfly hr (n + 1))).trans
        (by congr 1; simp only [tri]; ring)

theorem latency_sortOE (hr : r.latency = some L) (hd : d.latency = some L) :
    ∀ n, (sortOE r d n).latency = some (tri n * L)
  | 0 => by simp [sortOE, tri, latency_idC]
  | n + 1 => by
      exact (latency_seq (latency_two (latency_sortOE hr hd n)) (latency_mergeOE hr hd (n + 1))).trans
        (by congr 1; simp only [tri]; ring)

theorem latency_sortV (hr : r.latency = some L) (n : Nat) :
    (sortV r n).latency = some (n * (n * L)) :=
  latency_hrep (latency_vfly hr n) n

theorem latency_sortQ (hr : r.latency = some L) (hd : d.latency = some L) (n : Nat) :
    (sortQ r d n).latency = some (n * (n * L)) :=
  latency_hrep (latency_qfly hr hd n) n

end Ruby.Circuit
