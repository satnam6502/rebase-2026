import Ruby.NetlistLayout

/-!
# The netlist computes what the circuit means

An execution semantics for the instance list of a netlist: an environment gives
every port bit and internal node a value, and executing an instance sets the
nodes it drives (a LUT applies its function, a CARRY4 follows the UNISIM
equations `carry4Fn`, and a register passes its input, as in one cycle of
`Circuit.eval`).

`Circuit.gen_eval`: executing the instances that `Circuit.gen` emits, in
order, gives the output nets exactly the values `Circuit.eval` assigns. So the
netlist written out as SystemVerilog is the circuit that the theorems are
about. The wiring cases follow from naturality: renaming nets commutes with
evaluating them.
-/

namespace Ruby

open Shape

/-- Values of the port bits and internal nodes of a netlist. -/
structure Env where
  node : Nat → Bool
  port : String → List Nat → Bool

def Net.val (ρ : Env) : Net → Bool
  | .const b => b
  | .node i => ρ.node i
  | .port name path => ρ.port name path

/-- Set nodes `base … base + n - 1` to `g 0 … g (n - 1)`. -/
def Env.setBlock (ρ : Env) (base n : Nat) (g : Nat → Bool) : Env :=
  { ρ with node := fun j => if base ≤ j ∧ j < base + n then g (j - base) else ρ.node j }

/-- Execute one instance. -/
def InstKind.exec (ρ : Env) : InstKind → Env
  | .lut _ f ins o => ρ.setBlock o 1 fun _ => f fun j => (ins j).val ρ
  | .carry4 ci cy di s o =>
      let r := carry4Fn ((ci.val ρ, cy.val ρ), (fun i => (di i).val ρ, fun i => (s i).val ρ))
      ρ.setBlock o 8 fun j => if h : j < 4 then r.1 ⟨j, h⟩ else r.2 ⟨(j - 4) % 4, by omega⟩
  | .fdce d q => ρ.setBlock q 1 fun _ => d.val ρ

/-- Execute instances in order. -/
def execAll (ρ : Env) (L : List Inst) : Env := L.foldl (fun ρ i => i.kind.exec ρ) ρ

/-! ## Nets below a bound -/

/-- A net refers to no internal node at or above `n`. -/
def Net.Below (n : Nat) : Net → Prop
  | .node i => i < n
  | _ => True

instance (n : Nat) (net : Net) : Decidable (net.Below n) := by
  cases net <;> unfold Net.Below <;> infer_instance

/-- Every net of a bundle is below `n`. -/
def AllBelow (n : Nat) {s : Shape} (v : s.Val Net) : Prop :=
  s.map (fun net => decide (net.Below n)) v = Shape.fill true s

theorem map_const_eq_fill {β γ : Type} (c : γ) : (s : Shape) → (v : s.Val β) →
    s.map (fun _ => c) v = Shape.fill c s
  | .bit, _ => rfl
  | .pair a b, v => by simp [map_const_eq_fill c a, map_const_eq_fill c b, Shape.fill]
  | .vec _ a, v => by funext i; simp [map_const_eq_fill c a, Shape.fill]

theorem map_fill {β γ : Type} (f : β → γ) (c : β) : (s : Shape) → s.map f (Shape.fill c s) = Shape.fill (f c) s
  | .bit => rfl
  | .pair a b => by simp [map_fill f c a, map_fill f c b, Shape.fill]
  | .vec _ a => by funext i; simp [map_fill f c a, Shape.fill]

/-- Wiring keeps every net below a bound: it only routes nets and constants. -/
theorem allBelow_wire {a b : Shape} (w : Wiring a b) {n : Nat} {v : a.Val Net}
    (hv : AllBelow n v) : AllBelow n (w.run Net.const v) := by
  have hunit : w.run (fun _ => true) (Shape.fill true a) = Shape.fill true b := by
    have := w.natural (fun _ : Unit => true) (fun _ => ()) (Shape.fill () a)
    rw [map_const_eq_fill, map_fill] at this
    exact this.symm
  unfold AllBelow at hv ⊢
  rw [w.natural, hv]
  exact hunit

theorem allBelow_mono {n m : Nat} (h : n ≤ m) : {s : Shape} → {v : s.Val Net} → AllBelow n v →
    AllBelow m v
  | .bit, v, hv => by
      unfold AllBelow at hv ⊢
      cases v with
      | node i =>
          have hi : i < n := of_decide_eq_true hv
          exact decide_eq_true (show i < m by omega)
      | const b => rfl
      | port name path => rfl
  | .pair a b, v, hv => by
      unfold AllBelow at hv ⊢
      simp only [Shape.map_pair, Shape.fill, Prod.mk.injEq] at hv ⊢
      exact ⟨allBelow_mono h hv.1, allBelow_mono h hv.2⟩
  | .vec _ a, v, hv => by
      unfold AllBelow at hv ⊢
      funext i
      exact allBelow_mono h (congrFun hv i)

theorem allBelow_pair {n : Nat} {a b : Shape} {v : (Shape.pair a b).Val Net} :
    AllBelow n v ↔ AllBelow n v.1 ∧ AllBelow n v.2 := by
  unfold AllBelow
  simp [Shape.fill, Prod.ext_iff]

theorem allBelow_vec {n m : Nat} {a : Shape} {v : (Shape.vec m a).Val Net} :
    AllBelow n v ↔ ∀ i, AllBelow n (v i) := by
  unfold AllBelow
  simp only [Shape.map_vec, Shape.fill]
  exact funext_iff

/-- Environments that agree below `n` give the same values to nets below `n`. -/
theorem map_val_agree {n : Nat} {ρ ρ' : Env} (hnode : ∀ i < n, ρ'.node i = ρ.node i)
    (hport : ρ'.port = ρ.port) : {s : Shape} → {v : s.Val Net} → AllBelow n v →
      s.map (Net.val ρ') v = s.map (Net.val ρ) v
  | .bit, v, hv => by
      unfold AllBelow at hv
      cases v with
      | node i => exact hnode i (of_decide_eq_true hv)
      | const b => rfl
      | port name path => simp [Shape.map_bit, Net.val, hport]
  | .pair a b, v, hv => by
      rw [allBelow_pair] at hv
      simp only [Shape.map_pair, map_val_agree hnode hport hv.1, map_val_agree hnode hport hv.2]
  | .vec _ a, v, hv => by
      rw [allBelow_vec] at hv
      funext i
      exact map_val_agree hnode hport (hv i)

/-! ## Correctness of netlist generation -/

theorem execAll_append (ρ : Env) (L₁ L₂ : List Inst) :
    execAll ρ (L₁ ++ L₂) = execAll (execAll ρ L₁) L₂ := by
  simp [execAll, List.foldl_append]

/-- Running `m` from state `s` appends instances `L`; executed from `ρ`, they leave
the nodes below the old counter and the ports alone, and give the output nets
(all below the new counter) the values `X`. -/
def GenOK {b : Shape} (m : NetM (b.Val Net)) (s : NetlistState) (ρ : Env) (X : b.Val Bool) :
    Prop :=
  ∃ L : List Inst,
    (m.run s).2.insts.toList = s.insts.toList ++ L ∧
    s.nextNode ≤ (m.run s).2.nextNode ∧
    (∀ i < s.nextNode, (execAll ρ L).node i = ρ.node i) ∧
    (execAll ρ L).port = ρ.port ∧
    AllBelow (m.run s).2.nextNode (m.run s).1 ∧
    b.map (Net.val (execAll ρ L)) (m.run s).1 = X

theorem genOK_pure {b : Shape} (out : b.Val Net) (s : NetlistState) (ρ : Env) (X : b.Val Bool)
    (hb : AllBelow s.nextNode out) (hx : b.map (Net.val ρ) out = X) :
    GenOK (pure out : NetM (b.Val Net)) s ρ X :=
  ⟨[], by simp only [List.append_nil]; rfl, le_refl _, fun _ _ => rfl, rfl, hb, hx⟩

theorem genOK_bind {b c : Shape} {m : NetM (b.Val Net)} {f : b.Val Net → NetM (c.Val Net)}
    {s : NetlistState} {ρ : Env} {X : b.Val Bool} {Y : c.Val Bool} (hm : GenOK m s ρ X)
    (hf : ∀ (s' : NetlistState) (ρ' : Env) (u : b.Val Net), AllBelow s'.nextNode u →
      b.map (Net.val ρ') u = X → s.nextNode ≤ s'.nextNode →
      (∀ i < s.nextNode, ρ'.node i = ρ.node i) → ρ'.port = ρ.port → GenOK (f u) s' ρ' Y) :
    GenOK (m >>= f) s ρ Y := by
  obtain ⟨L₁, hL₁, hle₁, hpres₁, hport₁, hbelow₁, hval₁⟩ := hm
  obtain ⟨L₂, hL₂, hle₂, hpres₂, hport₂, hbelow₂, hval₂⟩ :=
    hf (m.run s).2 (execAll ρ L₁) (m.run s).1 hbelow₁ hval₁ hle₁ hpres₁ hport₁
  refine ⟨L₁ ++ L₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((f (m.run s).1).run (m.run s).2).2.insts.toList = _
    rw [hL₂, hL₁, List.append_assoc]
  · exact le_trans hle₁ hle₂
  · intro i hi
    rw [execAll_append, hpres₂ i (by omega), hpres₁ i hi]
  · rw [execAll_append, hport₂, hport₁]
  · exact hbelow₂
  · rw [execAll_append]; exact hval₂

/-- Changing the environment below the bound, the values of bounded nets stay. -/
theorem genOK_congr {b : Shape} {m : NetM (b.Val Net)} {s : NetlistState} {ρ : Env}
    {X X' : b.Val Bool} (h : GenOK m s ρ X) (hx : X = X') : GenOK m s ρ X' := hx ▸ h

theorem setBlock_node_lt (ρ : Env) (base n : Nat) (g : Nat → Bool) (i : Nat) (hi : i < base) :
    (ρ.setBlock base n g).node i = ρ.node i := by
  show (if base ≤ i ∧ i < base + n then g (i - base) else ρ.node i) = ρ.node i
  simp only [show ¬ (base ≤ i ∧ i < base + n) by omega, ↓reduceIte]

theorem setBlock_node_in (ρ : Env) (base n : Nat) (g : Nat → Bool) (j : Nat) (hj : j < n) :
    (ρ.setBlock base n g).node (base + j) = g j := by
  show (if base ≤ base + j ∧ base + j < base + n then g (base + j - base) else ρ.node (base + j)) = g j
  simp only [show base ≤ base + j ∧ base + j < base + n by omega, and_self, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem execAll_single (ρ : Env) (inst : Inst) : execAll ρ [inst] = inst.kind.exec ρ := rfl

theorem allBelow_node {n i : Nat} (h : i < n) : AllBelow (s := .bit) n (Net.node i) :=
  decide_eq_true h

theorem Prim.gen_ok {a b : Shape} (p : Prim a b) (x y : Nat) (v : a.Val Net) (s : NetlistState)
    (ρ : Env) (_hv : AllBelow s.nextNode v) :
    GenOK (p.gen x y v) s ρ (p.eval (a.map (Net.val ρ) v)) := by
  cases p with
  | lut k f =>
      refine ⟨[⟨s.insts.size, x, y, .lut k f v s.nextNode⟩], ?_, ?_, ?_, rfl, ?_, ?_⟩
      · show (s.insts.push _).toList = _; simp
      · show s.nextNode ≤ s.nextNode + 1; omega
      · intro i hi
        show (ρ.setBlock s.nextNode 1 fun _ => f fun j => (v j).val ρ).node i = ρ.node i
        exact setBlock_node_lt _ _ _ _ _ hi
      · exact allBelow_node (show s.nextNode < s.nextNode + 1 by omega)
      · show (ρ.setBlock s.nextNode 1 fun _ => f fun j => (v j).val ρ).node (s.nextNode + 0) = _
        exact setBlock_node_in ρ s.nextNode 1 _ 0 (by omega)
  | carry4 =>
      let R := carry4Fn ((v.1.1.val ρ, v.1.2.val ρ), (fun i => (v.2.1 i).val ρ, fun i => (v.2.2 i).val ρ))
      let g : Nat → Bool := fun j => if h : j < 4 then R.1 ⟨j, h⟩ else R.2 ⟨(j - 4) % 4, by omega⟩
      refine ⟨[⟨s.insts.size, x, y, .carry4 v.1.1 v.1.2 v.2.1 v.2.2 s.nextNode⟩], ?_, ?_, ?_, rfl,
        ?_, ?_⟩
      · show (s.insts.push _).toList = _; simp
      · show s.nextNode ≤ s.nextNode + 8; omega
      · intro i hi
        show (ρ.setBlock s.nextNode 8 g).node i = ρ.node i
        exact setBlock_node_lt _ _ _ _ _ hi
      · show AllBelow (s := Carry4Out) (s.nextNode + 8)
          ((fun i : Fin 4 => Net.node (s.nextNode + i.val)),
            (fun i : Fin 4 => Net.node (s.nextNode + 4 + i.val)))
        rw [allBelow_pair, allBelow_vec, allBelow_vec]
        exact ⟨fun i => allBelow_node (by have := i.isLt; omega),
          fun i => allBelow_node (by have := i.isLt; omega)⟩
      · refine Prod.ext ?_ ?_ <;> funext i <;> have hi := i.isLt
        · show (ρ.setBlock s.nextNode 8 g).node (s.nextNode + i.val) = R.1 i
          rw [setBlock_node_in _ _ _ _ _ (by omega)]
          simp only [g, hi, ↓reduceDIte]
        · show (ρ.setBlock s.nextNode 8 g).node (s.nextNode + 4 + i.val) = R.2 i
          rw [show s.nextNode + 4 + i.val = s.nextNode + (4 + i.val) by omega,
            setBlock_node_in _ _ _ _ _ (by omega)]
          simp only [g, show ¬ (4 + i.val < 4) by omega, ↓reduceDIte]
          exact congrArg R.2 (Fin.ext (by simp))
  | fdce =>
      refine ⟨[⟨s.insts.size, x, y, .fdce v s.nextNode⟩], ?_, ?_, ?_, rfl, ?_, ?_⟩
      · show (s.insts.push _).toList = _; simp
      · show s.nextNode ≤ s.nextNode + 1; omega
      · intro i hi
        show (ρ.setBlock s.nextNode 1 fun _ => v.val ρ).node i = ρ.node i
        exact setBlock_node_lt _ _ _ _ _ hi
      · exact allBelow_node (show s.nextNode < s.nextNode + 1 by omega)
      · show (ρ.setBlock s.nextNode 1 fun _ => v.val ρ).node (s.nextNode + 0) = _
        exact setBlock_node_in ρ s.nextNode 1 _ 0 (by omega)

/-- The `map` case: running one generator per index appends instances computing
each element, keeping the nodes below the starting counter. -/
theorem mapM_ok {n : Nat} {b : Shape} (g : Fin n → NetM (b.Val Net)) (X : Fin n → b.Val Bool)
    (s₀ : NetlistState) (ρ₀ : Env)
    (hg : ∀ i (s : NetlistState) (ρ : Env), s₀.nextNode ≤ s.nextNode →
      (∀ j < s₀.nextNode, ρ.node j = ρ₀.node j) → ρ.port = ρ₀.port → GenOK (g i) s ρ (X i)) :
    ∀ (l : List (Fin n)) (s : NetlistState) (ρ : Env), s₀.nextNode ≤ s.nextNode →
      (∀ j < s₀.nextNode, ρ.node j = ρ₀.node j) → ρ.port = ρ₀.port →
      ∃ L : List Inst,
        ((l.mapM g).run s).2.insts.toList = s.insts.toList ++ L ∧
        s.nextNode ≤ ((l.mapM g).run s).2.nextNode ∧
        (∀ j < s.nextNode, (execAll ρ L).node j = ρ.node j) ∧
        (execAll ρ L).port = ρ.port ∧
        ((l.mapM g).run s).1.length = l.length ∧
        ∀ (k : Nat) (hk : k < l.length),
          AllBelow ((l.mapM g).run s).2.nextNode
            (((l.mapM g).run s).1.getD k (Shape.fill (Net.const false) b)) ∧
          b.map (Net.val (execAll ρ L))
            (((l.mapM g).run s).1.getD k (Shape.fill (Net.const false) b)) = X (l[k]'hk)
  | [], s, ρ, _, _, _ => ⟨[], by simp only [List.append_nil]; rfl, le_refl _, fun _ _ => rfl, rfl,
      rfl, fun k hk => absurd hk (by simp)⟩
  | i :: l, s, ρ, hle, hagree, hport => by
      obtain ⟨L₁, hL₁, hle₁, hpres₁, hport₁, hbelow₁, hval₁⟩ := hg i s ρ hle hagree hport
      set s₁ := (g i).run s |>.2
      set u := (g i).run s |>.1
      obtain ⟨L₂, hL₂, hle₂, hpres₂, hport₂, hlen₂, hel₂⟩ :=
        mapM_ok g X s₀ ρ₀ hg l s₁ (execAll ρ L₁) (le_trans hle hle₁)
          (fun j hj => by rw [hpres₁ j (by omega), hagree j hj]) (by rw [hport₁, hport])
      have hrun : (List.mapM g (i :: l)).run s =
          (u :: ((l.mapM g).run s₁).1, ((l.mapM g).run s₁).2) := by
        rw [List.mapM_cons]; rfl
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hrun]; simp only; rw [hL₂, hL₁, List.append_assoc]
      · rw [hrun]; exact le_trans hle₁ hle₂
      · intro j hj; rw [execAll_append, hpres₂ j (by omega), hpres₁ j hj]
      · rw [execAll_append, hport₂, hport₁]
      · rw [hrun]; simp [hlen₂]
      · intro k hk
        rcases k with _ | k
        · simp only [hrun, List.getD_cons_zero, List.getElem_cons_zero]
          refine ⟨allBelow_mono hle₂ hbelow₁, ?_⟩
          rw [execAll_append, map_val_agree hpres₂ hport₂ hbelow₁, hval₁]
        · simp only [hrun, List.getD_cons_succ, List.getElem_cons_succ]
          have := hel₂ k (by simp at hk; omega)
          rw [execAll_append]
          exact this

/-- **Netlist generation is correct.** Executing the instances that `c.gen`
appends, from any environment, gives its output nets the values that
`Circuit.eval` assigns to the values of its input nets. -/
theorem Circuit.gen_eval : {a b : Shape} → (c : Circuit a b) → (x y : Nat) → (v : a.Val Net) →
    (s : NetlistState) → (ρ : Env) → AllBelow s.nextNode v →
    GenOK (c.gen x y v) s ρ (c.eval (a.map (Net.val ρ) v))
  | _, _, .prim p, x, y, v, s, ρ, hv => Prim.gen_ok p x y v s ρ hv
  | _, _, .wire w, _, _, v, s, ρ, hv => by
      refine genOK_pure _ s ρ _ (allBelow_wire w hv) ?_
      rw [w.natural]; rfl
  | _, _, .seq .beside r t, x, y, v, s, ρ, hv => by
      refine genOK_bind (Circuit.gen_eval r x y v s ρ hv) ?_
      intro s' ρ' u hu hval _ _ _
      have := Circuit.gen_eval t (x + r.size.1) y u s' ρ' hu
      rw [hval] at this
      exact this
  | _, _, .seq .below r t, x, y, v, s, ρ, hv => by
      refine genOK_bind (Circuit.gen_eval r x y v s ρ hv) ?_
      intro s' ρ' u hu hval _ _ _
      have := Circuit.gen_eval t x (y + r.size.2) u s' ρ' hu
      rw [hval] at this
      exact this
  | _, _, .seq .overlay r t, x, y, v, s, ρ, hv => by
      refine genOK_bind (Circuit.gen_eval r x y v s ρ hv) ?_
      intro s' ρ' u hu hval _ _ _
      have := Circuit.gen_eval t x y u s' ρ' hu
      rw [hval] at this
      exact this
  | _, _, .par r t, x, y, v, s, ρ, hv => by
      rw [allBelow_pair] at hv
      refine genOK_bind (Circuit.gen_eval r x y v.1 s ρ hv.1) ?_
      intro s₁ ρ₁ u hu hval₁ hle₁ hpres₁ hport₁
      refine genOK_bind (Circuit.gen_eval t x (y + r.size.2) v.2 s₁ ρ₁ (allBelow_mono hle₁ hv.2)) ?_
      intro s₂ ρ₂ w hw hval₂ hle₂ hpres₂ hport₂
      refine genOK_pure (b := Shape.pair _ _) (u, w) s₂ ρ₂ _ ?_ ?_
      · rw [allBelow_pair]; exact ⟨allBelow_mono hle₂ hu, hw⟩
      · simp only [Shape.map_pair]
        rw [map_val_agree (ρ := ρ₁) (ρ' := ρ₂) hpres₂ hport₂ hu, hval₁, hval₂,
          map_val_agree hpres₁ hport₁ hv.2]
        rfl
  | _, _, .map n r, x, y, v, s, ρ, hv => by
      rw [allBelow_vec] at hv
      have hm := mapM_ok (fun i : Fin n => r.gen x (y + i.val * r.size.2) (v i))
        (fun i => r.eval (Shape.map (Net.val ρ) _ (v i))) s ρ (fun i s' ρ' hle hagree hport => by
          have := Circuit.gen_eval r x (y + i.val * r.size.2) (v i) s' ρ' (allBelow_mono hle (hv i))
          rwa [map_val_agree hagree hport (hv i)] at this) (List.finRange n) s ρ (le_refl _)
        (fun _ _ => rfl) rfl
      obtain ⟨L, hL, hle, hpres, hport, hlen, hel⟩ := hm
      refine ⟨L, ?_, ?_, hpres, hport, ?_, ?_⟩
      · exact hL
      · exact hle
      · rw [allBelow_vec]
        intro i
        exact (hel i.val (by simp)).1
      · funext i
        have h := (hel i.val (by simp)).2
        have hi : (List.finRange n)[i.val]'(by simp) = i := by simp
        rw [hi] at h
        exact h

end Ruby

namespace Ruby

open Shape

theorem allBelow_portVal (n : Nat) (name : String) : (s : Shape) → (path : List Nat) →
    AllBelow n (Shape.portVal name s path)
  | .bit, _ => rfl
  | .pair a b, path => by
      rw [allBelow_pair]; exact ⟨allBelow_portVal n name a _, allBelow_portVal n name b _⟩
  | .vec _ a, path => by
      rw [allBelow_vec]; exact fun i => allBelow_portVal n name a _

/-- **The netlist of a module computes the circuit.** For any values of the input
port bits, executing every instance of `c.netlist` in order gives the output
nets the values that `Circuit.eval` gives the outputs. -/
theorem Circuit.netlist_correct {a b : Shape} (c : Circuit a b) (inName : String)
    (port : String → List Nat → Bool) :
    let ρ : Env := ⟨fun _ => false, port⟩
    b.map (Net.val (execAll ρ (c.netlist inName).2.insts.toList)) (c.netlist inName).1 =
      c.eval (a.map (Net.val ρ) (Shape.portVal inName a [])) := by
  intro ρ
  obtain ⟨L, hL, -, -, -, -, hval⟩ :=
    Circuit.gen_eval c 0 0 (Shape.portVal inName a []) {} ρ (allBelow_portVal 0 inName a [])
  have hL' : (c.netlist inName).2.insts.toList = L := by
    simpa [Circuit.netlist] using hL
  rw [hL']
  exact hval

end Ruby
