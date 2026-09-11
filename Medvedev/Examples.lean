import Medvedev.Reduction
import Medvedev.UpperBound

/-! # Small checks of conventions and boundary cases.
These supplement the universally quantified proofs; they do not replace them. -/

namespace Medvedev.Examples

open Formula

def oneTile : WangCode := ⟨0, fun _ _ => true, fun _ _ => true⟩
def noHorizontalEdge : WangCode := ⟨0, fun _ _ => false, fun _ _ => true⟩

theorem period_one : TilesTorus oneTile.system :=
  ⟨0, 0, ⟨{ tile := fun _ _ => 0, horizontal := fun _ _ => rfl, vertical := fun _ _ => rfl }⟩⟩

theorem period_one_formula_refutable : ¬ InML oneTile.formula := oneTile.correct.mp period_one

theorem forbidden_self_edge : ¬ TilesTorus noHorizontalEdge.system := by
  rintro ⟨m, n, ⟨τ⟩⟩
  have h := τ.horizontal 0 0
  change false = true at h
  cases h

theorem forbidden_self_edge_formula_valid : InML noHorizontalEdge.formula := by
  classical
  by_contra h
  exact forbidden_self_edge (noHorizontalEdge.correct.mpr h)

theorem equal_generator_supports : support (Mid.pos (T := Fin 1) .h) = support (.sep .h) := rfl
theorem generator_roles_distinct : (Mid.pos (T := Fin 1) .h) ≠ .sep .h := by decide
theorem smallest_compressed_carrier : Fintype.card (Compressed.Marker (Fin 1) (Fin 1) (Fin 1) × Colour (Fin 1)) = 48 := by
  rw [compressed_carrier_card]
  decide

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem identity_two_points : checkFrame (.imp (.atom 0) (.atom 0)) 1 = true := by decide
theorem bottom_singleton : checkFrame .bot 0 = false := by decide
theorem excluded_middle_two_points : checkFrame (.disj (.atom 0) (.imp (.atom 0) .bot)) 1 = false := by decide

end Medvedev.Examples
