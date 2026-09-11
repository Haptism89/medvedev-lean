import Medvedev.Domino.StandardTM

namespace Medvedev.Domino.BridgeAudit

/-- Every integer cell is represented, including all negative cells. -/
theorem address_covers (z : ℤ) : ∃ s i, FoldedTM.address s i = z := by
  cases z with
  | ofNat i => exact ⟨false, i, rfl⟩
  | negSucc i => exact ⟨true, i, by simp [FoldedTM.address]; omega⟩

theorem every_integer_cell {Q Γ : Type} [Inhabited Γ] {c : Turing.TM0.Cfg Γ Q}
    {d : AbsoluteCfg (Bool × Q) (FoldedTM.Symbol Γ)} (h : FoldedTM.Represents c d) (z : ℤ) :
    ∃ s i, FoldedTM.address s i = z ∧
      FoldedTM.read s (d.tape i) = c.Tape.nth (z - FoldedTM.address d.state.1 d.head) := by
  obtain ⟨s, i, rfl⟩ := address_covers z
  exact ⟨s, i, rfl, h.2.2 s i⟩

theorem left_from_zero_changes_track : FoldedTM.motion false true .left = (true, .stay) := rfl
theorem right_from_minus_one_changes_track : FoldedTM.motion true true .right = (false, .stay) := rfl
theorem left_on_negative_track : FoldedTM.motion true false .left = (true, .right) := rfl
theorem right_on_negative_track : FoldedTM.motion true false .right = (true, .left) := rfl

theorem write_preserves_other_track {Γ : Type} (s : Bool) (b : Γ) (a : FoldedTM.Symbol Γ) :
    FoldedTM.read (!s) (FoldedTM.write s b a) = FoldedTM.read (!s) a := by
  cases s <;> rfl

theorem write_preserves_origin_mark {Γ : Type} (s : Bool) (b : Γ) (a : FoldedTM.Symbol Γ) :
    (FoldedTM.write s b a).1 = a.1 := by cases s <;> rfl

/-- A fixed point with a defined successor cannot be a halting computation. -/
theorem fixed_step_not_halting {C : Type} (f : C → Option C) (c : C) (hf : f c = some c) :
    ¬ (Turing.eval f c).Dom := by
  intro h
  obtain ⟨hr, hs⟩ := Turing.mem_eval.mp (Part.get_mem h)
  have invariant : ∀ {d}, Turing.Reaches f c d → d = c := by
    intro d hd
    induction hd with
    | refl => rfl
    | @tail d e _ he ih =>
      subst d
      exact Option.some.inj (he.symm.trans hf)
  rw [invariant hr, hf] at hs
  cases hs

def haltNow : TM0Code := ⟨0, 0, []⟩
def leftForever : TM0Code := ⟨0, 0, [some (0, .inl .left)]⟩
def inputSensitive : TM0Code := ⟨0, 1, [some (0, .inr 0), none]⟩

/-- Write one at cell zero, then move left. The destination is blank on a
two-sided tape. A simulation that clips the left move would read one and loop. -/
def crossOrigin : TM0Code := ⟨2, 1,
  [some (1, .inr 1), some (1, .inr 1),
   some (2, .inl .left), some (2, .inl .left), none, some (2, .inr 1)]⟩

theorem haltNow_source_halts : (Turing.TM0.eval haltNow.machine []).Dom :=
  (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, rfl⟩).1

theorem input_one_halts : (Turing.TM0.eval inputSensitive.machine [1]).Dom :=
  (Turing.mem_eval.mpr ⟨Relation.ReflTransGen.refl, rfl⟩).1

theorem input_empty_does_not_halt : ¬ (Turing.TM0.eval inputSensitive.machine []).Dom :=
  fixed_step_not_halting _ _ rfl

theorem leftForever_does_not_halt : ¬ (Turing.TM0.eval leftForever.machine []).Dom := by
  intro h
  obtain ⟨_, hs⟩ := Turing.mem_eval.mp
    (Part.get_mem (show (Turing.eval (Turing.TM0.step leftForever.machine) (Turing.TM0.init [])).Dom from h))
  have ht : ∀ c : Turing.TM0.Cfg (Fin 1) (Fin 1), Turing.TM0.step leftForever.machine c ≠ none := by
    intro c
    have hq : c.q = 0 := Subsingleton.elim _ _
    have ha : c.Tape.head = 0 := Subsingleton.elim _ _
    simp [Turing.TM0.step, TM0Code.machine, leftForever, hq, ha]
  exact ht _ hs

theorem crossOrigin_source_halts : (Turing.TM0.eval crossOrigin.machine []).Dom := by
  let c₀ : Turing.TM0.Cfg (Fin 2) (Fin 3) := Turing.TM0.init []
  let c₁ : Turing.TM0.Cfg (Fin 2) (Fin 3) := ⟨1, c₀.Tape.write 1⟩
  let c₂ : Turing.TM0.Cfg (Fin 2) (Fin 3) := ⟨2, c₁.Tape.move .left⟩
  have h₁ : Turing.TM0.step crossOrigin.machine c₀ = some c₁ := rfl
  have h₂ : Turing.TM0.step crossOrigin.machine c₁ = some c₂ := rfl
  have hs : Turing.TM0.step crossOrigin.machine c₂ = none := rfl
  have hr : Turing.Reaches (Turing.TM0.step crossOrigin.machine) c₀ c₁ := .single h₁
  exact (Turing.mem_eval.mpr ⟨hr.tail h₂, hs⟩).1

/-- The tempting direct translation, which keeps the one-sided boundary,
changes the answer on `crossOrigin`. This is a proved negative control. -/
def incorrectlyClipped : MachineCode := ⟨2, 1,
  [some (1, 1, .stay), some (1, 1, .stay),
   some (2, 0, .left), some (2, 1, .left), none, some (2, 1, .stay)]⟩

theorem incorrectlyClipped_does_not_halt : ¬ incorrectlyClipped.Halts := by
  let M := incorrectlyClipped.machine
  let c₁ : TapeCfg (Fin 3) (Fin 2) := ⟨1, [], 1, []⟩
  let c₂ : TapeCfg (Fin 3) (Fin 2) := ⟨2, [], 1, []⟩
  have h₁ : M.step M.initialCfg = some c₁ := rfl
  have h₂ : M.step c₁ = some c₂ := rfl
  have hf : M.step c₂ = some c₂ := rfl
  have lift : ∀ {c d}, M.step c = some d →
      M.absoluteStep (c.absolute M.blank) = some (d.absolute M.blank) := by
    intro c d h
    rw [← M.absolute_step, h]
    rfl
  have hr : Turing.Reaches M.absoluteStep (M.initialCfg.absolute M.blank)
      (c₁.absolute M.blank) := .single (lift h₁)
  change ¬ M.Halts
  rw [M.halts_iff_eval, ← M.absolute_initial, Turing.reaches_eval (hr.tail (lift h₂))]
  exact fixed_step_not_halting _ _ (lift hf)

theorem compiled_empty_immediate_halt : (haltNow.compile []).Halts :=
  (haltNow.halts_iff []).mpr haltNow_source_halts

theorem compiled_crossOrigin_halts : (crossOrigin.compile []).Halts :=
  (crossOrigin.halts_iff []).mpr crossOrigin_source_halts

theorem compiled_input_one_halts : (inputSensitive.compile [1]).Halts :=
  (inputSensitive.halts_iff [1]).mpr input_one_halts

theorem compiled_input_empty_never_halts : ¬ (inputSensitive.compile []).Halts :=
  fun h => input_empty_does_not_halt ((inputSensitive.halts_iff []).mp h)

theorem compiled_leftForever_never_halts : ¬ (leftForever.compile []).Halts :=
  fun h => leftForever_does_not_halt ((leftForever.halts_iff []).mp h)

theorem leftForever_formula_valid : Formula.InML (leftForever.compile []).formula :=
  (leftForever.nonhalting_iff_valid []).mp leftForever_does_not_halt

theorem crossOrigin_formula_invalid : ¬ Formula.InML (crossOrigin.compile []).formula :=
  fun h => ((crossOrigin.nonhalting_iff_valid []).mpr h) crossOrigin_source_halts

end Medvedev.Domino.BridgeAudit
