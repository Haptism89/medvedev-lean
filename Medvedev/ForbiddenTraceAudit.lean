import Medvedev.ReviewChecks

/-!
An independent statement of the manuscript's forbidden-trace lemma (1663–1680).
The generic theorem needs only the domain restriction and H1(a), with no
realization, demand response, principalization, or finiteness premise.
-/

namespace Medvedev.ForbiddenTraceAudit

variable {K P : Type} [Preorder P]

/-- A role is visible when some assigned subset carries that exact role. -/
def trace (f : Set K → Option P) (X : Set K) : Set P :=
  {p | ∃ E, E ⊆ X ∧ f E = some p}

/-- H2 for one fixed pair of roles, universally over its concrete inputs. -/
def Responds (f : Set K → Option P) (p q : P) : Prop :=
  ∀ E F, f E = some p → f F = some q →
    ∃ Z r, Z.Nonempty ∧ Z ⊆ E ∪ F ∧ f Z = some r ∧ ¬ p ≤ r ∧ ¬ q ≤ r

/-- Only the domain condition and H1(a) are needed for the equivalence.
In particular, neither direction assumes the response condition it proves. -/
theorem responds_iff_no_forbidden (f : Set K → Option P)
    (domain : ∀ X r, f X = some r → X.Nonempty)
    (back : ∀ E p r, f E = some p → p ≤ r → ∃ Z, Z ⊆ E ∧ f Z = some r)
    (p q : P) :
    Responds f p q ↔ ∀ X, X.Nonempty → trace f X ≠ {r | p ≤ r ∨ q ≤ r} := by
  constructor
  · intro response X _ he
    have hp : p ∈ trace f X := he ▸ Or.inl (le_refl p)
    have hq : q ∈ trace f X := he ▸ Or.inr (le_refl q)
    obtain ⟨E, hEX, hE⟩ := hp
    obtain ⟨F, hFX, hF⟩ := hq
    obtain ⟨Z, r, _, hZ, hr, hpr, hqr⟩ := response E F hE hF
    have visible : r ∈ trace f X := ⟨Z, hZ.trans (Set.union_subset hEX hFX), hr⟩
    rw [he] at visible
    exact visible.elim hpr hqr
  · intro forbidden E F hE hF
    have hnonempty : (E ∪ F).Nonempty := (domain E p hE).mono Set.subset_union_left
    have cover : {r | p ≤ r ∨ q ≤ r} ⊆ trace f (E ∪ F) := by
      intro r hr
      rcases hr with hp | hq
      · obtain ⟨Z, hZE, hZ⟩ := back E p r hE hp
        exact ⟨Z, hZE.trans Set.subset_union_left, hZ⟩
      · obtain ⟨Z, hZF, hZ⟩ := back F q r hF hq
        exact ⟨Z, hZF.trans Set.subset_union_right, hZ⟩
    have outside : ∃ r ∈ trace f (E ∪ F), ¬ (p ≤ r ∨ q ≤ r) := by
      classical
      by_contra hn
      apply forbidden (E ∪ F) hnonempty
      apply Set.Subset.antisymm _ cover
      intro r hr
      by_contra hnot
      exact hn ⟨r, hr, hnot⟩
    obtain ⟨r, ⟨Z, hZ, hr⟩, hout⟩ := outside
    exact ⟨Z, r, domain Z r hr, hZ, hr,
      fun hp => hout (Or.inl hp), fun hq => hout (Or.inr hq)⟩

variable {T : Type} [DecidableEq T]

/-- The graph trace agrees with the trace already used in recognition. -/
theorem realization_trace (D : Wang T) (R : Realization D K) (X : Set K) :
    trace R.toPartialFunction X = R.trace X := by
  ext p
  simp only [trace, Realization.trace, Set.mem_setOf_eq, R.toPartialFunction_spec]

/-- Literal H0/H1 premises, without H2, suffice for the complete paper lemma.
The right side quantifies every demand and every nonempty world independently. -/
theorem partialConditions_iff_no_forbidden (D : Wang T) (f : Set K → Option (Role T))
    (domain : ∀ X p, f X = some p → X.Nonempty)
    (base : f Set.univ = some .root)
    (singleton : ∀ k, ∃ c, f {k} = some (.max c))
    (back : ∀ X p q, f X = some p → p ≤ q → ∃ Y, Y ⊆ X ∧ f Y = some q)
    (forth : ∀ X Y p q, f X = some p → f Y = some q → Y ⊆ X → p ≤ q) :
    Review.PartialConditions D f ↔ ∀ a b, demand D a b →
      ∀ X, X.Nonempty → trace f X ≠ upset (.mid a) ∪ upset (.mid b) := by
  constructor
  · intro h a b hd
    apply (responds_iff_no_forbidden f domain back (.mid a) (.mid b)).mp
    intro E F hE hF
    obtain ⟨Z, r, hZ, hr, hout⟩ := h.response a b E F hd hE hF
    exact ⟨Z, r, domain Z r hr, hZ, hr,
      fun ha => hout (Or.inl ha), fun hb => hout (Or.inr hb)⟩
  · intro h
    refine ⟨domain, base, singleton, back, forth, ?_⟩
    intro a b E F hd hE hF
    have response := (responds_iff_no_forbidden f domain back (.mid a) (.mid b)).mpr (h a b hd)
    obtain ⟨Z, r, _, hZ, hr, ha, hb⟩ := response E F hE hF
    exact ⟨Z, r, hZ, hr, fun hout => hout.elim ha hb⟩

/-- Two incomparable Mid-roles, assigned only to different singleton inputs. -/
noncomputable def missingSuccessors (X : Set Bool) : Option (Role Unit) := by
  classical
  exact if X = {false} then some (.mid (.pos .h))
    else if X = {true} then some (.mid (.pos .v)) else none

theorem missingSuccessors_values {X : Set Bool} {r : Role Unit}
    (h : missingSuccessors X = some r) : r = .mid (.pos .h) ∨ r = .mid (.pos .v) := by
  classical
  unfold missingSuccessors at h
  split_ifs at h <;> simp_all

/-- Without H1(a), inequality of traces alone need not produce an outside
role: a trace can be too small. The inputs here have distinct demanded shapes,
and the domain is nonempty wherever a role is assigned. -/
theorem forbidden_inequality_without_back_is_insufficient :
    (∀ X r, missingSuccessors X = some r → X.Nonempty) ∧
    (∀ X, X.Nonempty → trace missingSuccessors X ≠
      upset (.mid (.pos .h)) ∪ upset (.mid (.pos .v))) ∧
    ¬ Responds missingSuccessors (.mid (.pos .h)) (.mid (.pos .v)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro X r hr
    unfold missingSuccessors at hr
    split_ifs at hr with h h
    · exact h ▸ Set.singleton_nonempty false
    · exact h ▸ Set.singleton_nonempty true
  · intro X _ he
    have visible : (Role.max (.same .h) : Role Unit) ∈ trace missingSuccessors X := by
      rw [he]
      exact Or.inl (by simp [upset, support])
    obtain ⟨E, _, hE⟩ := visible
    rcases missingSuccessors_values hE with h | h <;> cases h
  · intro h
    have left : missingSuccessors {false} = some (.mid (.pos .h)) := by
      simp [missingSuccessors]
    have right : missingSuccessors {true} = some (.mid (.pos .v)) := by
      simp [missingSuccessors, Set.singleton_eq_singleton_iff]
    obtain ⟨Z, r, _, _, hr, hp, hq⟩ := h {false} {true} left right
    rcases missingSuccessors_values hr with rfl | rfl
    · exact hp (le_refl _)
    · exact hq (le_refl _)

end Medvedev.ForbiddenTraceAudit
