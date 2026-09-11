import Medvedev.Basic
import Mathlib.Tactic.CasesM

namespace Medvedev

variable {T : Type} [DecidableEq T]

/-- Executable presentation of the inductive D1--D7 relation. -/
def demandCode (D : Wang T) : Mid T → Mid T → Prop
  | .pos a, .notNext b => a = b
  | .sep a, .notSame b => a = b
  | .pos .h, .pos .v => True
  | .cell t, .provider (.source _ u) => t = u
  | .cell t, .provider (.candidate _ u) => t = u
  | .sep a, .provider (.step b) => a = b
  | .source a _, .step b => a = b
  | .expected a t, .candidate b u => a = b ∧ ¬ D.compat a t u
  | _, _ => False

instance (D : Wang T) [DecidableRel D.horizontal] [DecidableRel D.vertical] :
    DecidableRel (demandCode D) := fun a b => by
  cases a <;> cases b <;> (try cases_type* Axis Key) <;>
    dsimp [demandCode, Wang.compat] <;> infer_instance

set_option maxHeartbeats 3000000

omit [DecidableEq T] in
theorem demandCode_iff (D : Wang T) (a b : Mid T) :
    demandCode D a b ↔ OrientedDemand D a b := by
  constructor
  · intro h
    cases a <;> cases b <;> (try cases_type* Axis Key) <;>
      simp_all [demandCode] <;> subst_vars <;>
      first | exact .generate _ | exact .separate _ | exact .cell
            | exact .source _ _ | exact .candidate _ _ | exact .step _
            | exact .expected _ _ | exact .forbidden _ _ _ h
  · intro h
    cases h <;> (try cases_type* Axis) <;> simp_all [demandCode]

end Medvedev
