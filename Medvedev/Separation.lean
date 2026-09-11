import Medvedev.Compressed

namespace Medvedev.Compressed

variable {I J T : Type} [DecidableEq I] [DecidableEq J] [DecidableEq T]

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The finite symbolic check underlying Lemma `lem:compressed-separation`.
Containment must preserve supports and reverse the blocklist inclusions.
These two necessary conditions already force equality of roles. -/
theorem role_eq_of_column_constraints (τ : I → J → T) (pI : I → I) (pJ : J → J)
    (i₀ : I) (j₀ : J) (s t : State I J T)
    (hs : ∀ c ∈ support (stateRole τ s), c ∈ support (stateRole τ t))
    (hb : ∀ c ∈ support (stateRole τ s), ∀ u ∈ blocks pI pJ i₀ j₀ t c,
      u ∈ blocks pI pJ i₀ j₀ s c) :
    stateRole τ s = stateRole τ t := by
  cases s <;> cases t <;> (try cases_type* Axis Location Key) <;>
    simp_all [stateRole, support, blocks, cellBlocks, tile, Axis.other,
      or_imp, forall_and, eq_comm]

end Medvedev.Compressed
