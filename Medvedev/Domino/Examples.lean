import Medvedev.Domino.MachineCode

namespace Medvedev.Domino.Examples

def haltNow : MachineCode := ⟨0, 0, []⟩
def loopStay : MachineCode := ⟨0, 0, [some (0, 0, .stay)]⟩
def loopRight : MachineCode := ⟨0, 0, [some (0, 0, .right)]⟩
def haltAfterRight : MachineCode := ⟨1, 0, [some (1, 0, .right), none]⟩
def haltAfterLeft : MachineCode := ⟨1, 0, [some (1, 0, .left), none]⟩

theorem haltNow_halts : haltNow.Halts :=
  ⟨haltNow.machine.initialCfg, .refl, rfl⟩

/-- This checks both the implicit blank beyond the initial tape and halting
in the newly reached state, without imposing a finite tape bound. -/
theorem haltAfterRight_halts : haltAfterRight.Halts := by
  let target : TapeCfg (Fin 2) (Fin 1) := ⟨1, [0], 0, []⟩
  exact ⟨target, Relation.ReflTransGen.single rfl, rfl⟩

/-- A left move at position zero writes and changes state, staying at zero. -/
theorem haltAfterLeft_halts : haltAfterLeft.Halts := by
  let target : TapeCfg (Fin 2) (Fin 1) := ⟨1, [], 0, []⟩
  exact ⟨target, Relation.ReflTransGen.single rfl, rfl⟩

theorem loopStay_never_halts : ¬ loopStay.Halts := by
  rintro ⟨c, _, h⟩
  have hq : c.state = 0 := @Subsingleton.elim (Fin 1) _ _ _
  have ha : c.current = 0 := @Subsingleton.elim (Fin 1) _ _ _
  simp [MachineCode.machine, loopStay, hq, ha] at h

theorem loopRight_never_halts : ¬ loopRight.Halts := by
  rintro ⟨c, _, h⟩
  have hq : c.state = 0 := @Subsingleton.elim (Fin 1) _ _ _
  have ha : c.current = 0 := @Subsingleton.elim (Fin 1) _ _ _
  simp [MachineCode.machine, loopRight, hq, ha] at h

theorem haltNow_tiles : TilesTorus haltNow.domino.system := haltNow.domino_correct.mpr haltNow_halts
theorem rightLoop_has_no_torus : ¬ TilesTorus loopRight.domino.system :=
  fun h => loopRight_never_halts (loopRight.domino_correct.mp h)
theorem stayLoop_formula_valid : Formula.InML loopStay.formula :=
  loopStay.nonhalting_iff_valid.mp loopStay_never_halts
theorem haltNow_formula_invalid : ¬ Formula.InML haltNow.formula :=
  fun h => (haltNow.nonhalting_iff_valid.mpr h) haltNow_halts

theorem out_of_range_halts :
    (⟨0, 0, [some (1, 0, .stay)]⟩ : MachineCode).Halts :=
  ⟨_, .refl, rfl⟩

end Medvedev.Domino.Examples
