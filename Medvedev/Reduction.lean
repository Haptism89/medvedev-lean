import Medvedev.Recognition
import Medvedev.Renaming
import Medvedev.Counts

namespace Medvedev

open Formula

/-- An explicit input format: a positive number of tile types and two
directed Boolean compatibility tables. This excludes an empty tileset. -/
structure WangCode where
  size : ℕ
  horizontal : Fin (size + 1) → Fin (size + 1) → Bool
  vertical : Fin (size + 1) → Fin (size + 1) → Bool

def WangCode.system (c : WangCode) : Wang (Fin (c.size + 1)) where
  horizontal t u := c.horizontal t u = true
  vertical t u := c.vertical t u = true

instance (c : WangCode) : DecidableRel c.system.horizontal := fun _ _ => inferInstanceAs (Decidable (_ = true))
instance (c : WangCode) : DecidableRel c.system.vertical := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- An executable transformation into a single, fixed countable alphabet.
There is no choice of a valuation or a tiling in this definition. -/
def WangCode.formula (c : WangCode) : Formula ℕ :=
  rename Encodable.encode (alpha c.system)

/-- The central reduction, with a fixed natural-number variable alphabet. -/
theorem WangCode.correct (c : WangCode) :
    TilesTorus c.system ↔ ¬ InML c.formula := by
  rw [formula, inML_rename_iff _ Encodable.encode_injective]
  exact tiling_iff_not_valid c.system

/-- The exact logical use of the imported periodic-domino theorem.
`Machine`, `halts`, the map `domino`, and its correctness are explicit
parameters. In particular, the imported theorem is not a hidden axiom. -/
theorem nonhalting_reduction {Machine : Type} (halts : Machine → Prop)
    (domino : Machine → WangCode)
    (periodic_domino : ∀ M, halts M ↔ TilesTorus (domino M).system) (M : Machine) :
    ¬ halts M ↔ InML (domino M).formula := by
  classical
  rw [periodic_domino M, (domino M).correct, not_not]

end Medvedev
