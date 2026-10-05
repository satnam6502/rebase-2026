import Ruby.Netlist

/-!
# The netlist is placed as the layout semantics says

`Circuit.gen` emits one placed instance per primitive. The sites those
instances occupy, in emission order, are exactly `Circuit.sites`
(`gen_sites`). So the `RLOC` and `BEL` attributes written into the
SystemVerilog are the placement that the layout theorems
(`Circuit.nodup_sites`, `Circuit.sites_inBox`, the sorter sizes and densities)
are about.
-/

namespace Ruby

open Shape

/-- The sites occupied by a placed instance. -/
def Inst.footprint (i : Inst) : List (Nat × Nat × Site) :=
  match i.kind with
  | .lut .. => [(i.x, i.y, .lut)]
  | .carry4 .. => [(i.x, i.y, .carry), (i.x, i.y + 1, .carry), (i.x, i.y + 2, .carry),
      (i.x, i.y + 3, .carry)]
  | .fdce .. => [(i.x, i.y, .ff)]

/-- Running `m` appends instances that occupy exactly the sites `F`. -/
def EmitsSites {β : Type} (m : NetM β) (F : List (Nat × Nat × Site)) : Prop :=
  ∀ s : NetlistState, ∃ L : List Inst,
    ((m.run s).2.insts.toList = s.insts.toList ++ L) ∧ L.flatMap Inst.footprint = F

namespace EmitsSites

variable {β γ : Type}

theorem pure' (b : β) : EmitsSites (pure b : NetM β) [] :=
  fun s => ⟨[], by simp only [List.append_nil]; rfl, rfl⟩

theorem bind {m : NetM β} {f : β → NetM γ} {F G : List (Nat × Nat × Site)}
    (hm : EmitsSites m F) (hf : ∀ b, EmitsSites (f b) G) : EmitsSites (m >>= f) (F ++ G) := by
  intro s
  obtain ⟨L₁, h₁, hF⟩ := hm s
  obtain ⟨L₂, h₂, hG⟩ := hf (m.run s).1 (m.run s).2
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · simp only [StateT.run_bind] at *
    change ((f (m.run s).1).run (m.run s).2).2.insts.toList = _
    rw [h₂, h₁, List.append_assoc]
  · rw [List.flatMap_append, hF, hG]

theorem mapM {α : Type} (g : α → NetM β) (F : α → List (Nat × Nat × Site))
    (h : ∀ a, EmitsSites (g a) (F a)) : ∀ l : List α, EmitsSites (l.mapM g) (l.flatMap F)
  | [] => by simpa using pure' ([] : List β)
  | a :: l => by
      rw [List.mapM_cons, List.flatMap_cons]
      have := bind (h a) (fun b => (bind (mapM g F h l) (fun bs => pure' (b :: bs))))
      simpa using this

end EmitsSites

theorem emitInst_sites (x y : Nat) (k : InstKind) (F : List (Nat × Nat × Site))
    (hF : Inst.footprint ⟨0, x, y, k⟩ = F) : EmitsSites (emitInst x y k) F := by
  intro s
  refine ⟨[⟨s.insts.size, x, y, k⟩], ?_, ?_⟩
  · show (s.insts.push _).toList = _
    simp
  · rw [← hF]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    cases k <;> rfl

theorem freshBlock_sites (n : Nat) : EmitsSites (freshBlock n) [] :=
  fun s => ⟨[], by simp only [List.append_nil]; rfl, rfl⟩

theorem Prim.gen_sites {a b : Shape} (p : Prim a b) (x y : Nat) (v : a.Val Net) :
    EmitsSites (p.gen x y v) (p.footprint.map fun q => (x + q.1, y + q.2.1, q.2.2)) := by
  cases p with
  | lut k f =>
      have := EmitsSites.bind (freshBlock_sites 1) fun o =>
        EmitsSites.bind (emitInst_sites x y (.lut k f v o) [(x, y, .lut)] rfl)
          fun _ => EmitsSites.pure' (Net.node o)
      simpa [Prim.gen, Prim.footprint, Inst.footprint] using this
  | carry4 =>
      have := EmitsSites.bind (freshBlock_sites 8) fun o =>
        EmitsSites.bind (emitInst_sites x y (.carry4 v.1.1 v.1.2 v.2.1 v.2.2 o)
          [(x, y, .carry), (x, y + 1, .carry), (x, y + 2, .carry), (x, y + 3, .carry)] rfl)
          fun _ => EmitsSites.pure'
            ((fun i : Fin 4 => Net.node (o + i.val)), (fun i : Fin 4 => Net.node (o + 4 + i.val)))
      simpa [Prim.gen, Prim.footprint, Inst.footprint] using this
  | fdce =>
      have := EmitsSites.bind (freshBlock_sites 1) fun q =>
        EmitsSites.bind (emitInst_sites x y (.fdce v q) [(x, y, .ff)] rfl) fun _ =>
          EmitsSites.pure' (Net.node q)
      simpa [Prim.gen, Prim.footprint, Inst.footprint] using this

/-- **The emitted netlist occupies exactly the sites of the layout semantics.** -/
theorem Circuit.gen_sites : {a b : Shape} → (c : Circuit a b) → (x y : Nat) → (v : a.Val Net) →
    EmitsSites (c.gen x y v) (c.sites x y)
  | _, _, .prim p, x, y, v => Prim.gen_sites p x y v
  | _, _, .wire _, _, _, _ => EmitsSites.pure' _
  | _, _, .seq .beside r s, x, y, v => by
      simpa [Circuit.gen, Circuit.sites] using
        EmitsSites.bind (Circuit.gen_sites r x y v) fun u => Circuit.gen_sites s _ y u
  | _, _, .seq .below r s, x, y, v => by
      simpa [Circuit.gen, Circuit.sites] using
        EmitsSites.bind (Circuit.gen_sites r x y v) fun u => Circuit.gen_sites s x _ u
  | _, _, .seq .overlay r s, x, y, v => by
      simpa [Circuit.gen, Circuit.sites] using
        EmitsSites.bind (Circuit.gen_sites r x y v) fun u => Circuit.gen_sites s x y u
  | _, _, .par r s, x, y, v => by
      have := EmitsSites.bind (Circuit.gen_sites r x y v.1) fun u =>
        EmitsSites.bind (Circuit.gen_sites s x (y + r.size.2) v.2) fun w => EmitsSites.pure' (u, w)
      simpa [Circuit.gen, Circuit.sites] using this
  | _, _, .map n r, x, y, v => by
      have hm := EmitsSites.mapM (fun i : Fin n => r.gen x (y + i.val * r.size.2) (v i))
        (fun i => r.sites x (y + i.val * r.size.2)) (fun i => Circuit.gen_sites r _ _ (v i))
        (List.finRange n)
      have := EmitsSites.bind hm fun outs =>
        EmitsSites.pure' (fun i : Fin n => outs.getD i.val (Shape.fill (Net.const false) _))
      have hrange : (List.finRange n).flatMap (fun i => r.sites x (y + i.val * r.size.2)) =
          (List.range n).flatMap (fun i => r.sites x (y + i * r.size.2)) := by
        rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
      simpa [Circuit.gen, Circuit.sites, hrange] using this

end Ruby
