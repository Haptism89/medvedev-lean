import Medvedev.Clauses

namespace Medvedev

open Formula

variable {T K : Type} [DecidableEq T] [Fintype T] [Encodable T] {D : Wang T}

def Realization.traceValuation (R : Realization D K) (p : Role T) (X : Set K) : Prop :=
  p ∉ R.trace X

omit [Fintype T] [Encodable T] in
theorem Realization.traceValuation_persistent (R : Realization D K) : Persistent R.traceValuation := by
  intro p X Y _ hYX hp hpy
  exact hp (R.trace_mono hYX hpy)

theorem Realization.trace_clauses (R : Realization D K) (X : Set K) :
    ClauseFacts D R.traceValuation X := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Y hY _ hN
    obtain ⟨p, hp⟩ := R.trace_nonempty hY
    exact (forces_N _ _).mp hN p hp
  · intro a Y _ _ ha hr
    exact ha (R.trace_upward hr (root_le _))
  · intro a c hc Y _ _ hmax hmid
    exact hmax (R.trace_upward hmid hc)
  · intro p _ Y _ _ hinner
    by_contra hn
    have hp : p ∈ R.trace Y := Classical.not_not.mp hn
    obtain ⟨E, hEY, hE⟩ := hp
    have hA : Forces R.traceValuation E (AFormula p) := by
      apply (forces_A _ _ _).mpr
      intro q hnq hq
      exact hnq (by rwa [R.trace_principal hE] at hq)
    exact hinner E (R.nonempty hE) hEY hA ⟨E, Set.Subset.refl _, hE⟩
  · intro a b hd Y _ _ hA
    by_contra hn
    have ha : Role.mid a ∈ R.trace Y := by
      by_contra hna
      exact hn (Or.inl hna)
    have hb : Role.mid b ∈ R.trace Y := by
      by_contra hnb
      exact hn (Or.inr hnb)
    apply R.no_forbidden_trace (Or.inl hd) Y
    apply Set.Subset.antisymm
    · intro p hp
      by_contra hnp
      exact (forces_pair _ _ _ _).mp hA p (fun h => hnp (Or.inl h))
        (fun h => hnp (Or.inr h)) hp
    · intro p hp
      exact hp.elim (R.trace_upward ha) (R.trace_upward hb)

/-- Proposition `prop:recognition-forward`, for the actual formula syntax. -/
theorem Realization.refutes_alpha [DecidableRel D.horizontal] [DecidableRel D.vertical]
    (R : Realization D K) : ¬ FrameValid K (alpha D) := by
  intro hvalid
  have h := hvalid R.traceValuation R.traceValuation_persistent Set.univ (R.nonempty R.base)
  apply h Set.univ (R.nonempty R.base) (Set.Subset.refl _)
    ((forces_gamma_iff D _ _).mpr (R.trace_clauses _))
  exact ⟨Set.univ, Set.Subset.refl _, R.base⟩

end Medvedev
