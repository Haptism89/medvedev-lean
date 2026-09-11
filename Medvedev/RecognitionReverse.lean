import Medvedev.Clauses

namespace Medvedev

open Formula

variable {T K : Type} [DecidableEq T] [Fintype T] [Encodable T] {D : Wang T}

/-- Lemmas `lem:G` and `lem:climb`, with the trace properties derived from
the formula clauses rather than assumed. -/
def candidateTraceModel (v : Role T → Set K → Prop) (hv : Persistent v)
    (h : ClauseFacts D v Set.univ) (hne : (Set.univ : Set K).Nonempty)
    (hroot : ¬ v .root Set.univ) : TraceModel D K := by
  classical
  let G : Set K → Set (Role T) := fun X => {p | ¬ v p X}
  have up : ∀ {X : Set K} {p q : Role T}, X.Nonempty → ¬ v p X → p ≤ q → ¬ v q X := by
    intro X p q hX hp hpq
    cases p with
    | root =>
      cases q with
      | root => exact hp
      | mid a => exact fun ha => hp (h.Oroot a X hX (Set.subset_univ _) ha)
      | max c =>
        obtain ⟨a, hc⟩ := colour_has_provider c
        exact fun hmax => hp (h.Oroot a X hX (Set.subset_univ _)
          (h.Omax a c hc X hX (Set.subset_univ _) hmax))
    | mid a =>
      cases q with
      | root => exact False.elim hpq
      | mid b => have he : a = b := hpq; subst b; exact hp
      | max c => exact fun hc => hp (h.Omax a c hpq X hX (Set.subset_univ _) hc)
    | max c =>
      cases q with
      | root => exact False.elim hpq
      | mid _ => exact False.elim hpq
      | max d => have he : c = d := hpq; subst d; exact hp
  have principal : ∀ {X : Set K} {p : Role T}, X.Nonempty → p ∈ G X →
      ∃ Y, Y.Nonempty ∧ Y ⊆ X ∧ G Y = upset p := by
    intro X p hX hp
    by_cases hr : p = .root
    · subst p
      refine ⟨X, hX, Set.Subset.refl _, ?_⟩
      ext q
      exact ⟨fun _ => root_le q, fun hpq => up hX hp hpq⟩
    · have hinner : ¬ Forces v X (.imp (AFormula p) (.atom p)) := by
        intro hinner
        exact hp (h.B p hr X hX (Set.subset_univ _) hinner)
      obtain ⟨Y, hY, hYX, hA, hpY⟩ := (not_forces_imp v X (AFormula p) (.atom p)).mp hinner
      refine ⟨Y, hY, hYX, ?_⟩
      ext q
      constructor
      · intro hq
        by_contra hnq
        exact hq ((forces_A v Y p).mp hA q hnq)
      · intro hpq
        exact up hY hpY hpq
  have forbidden : ∀ {a b : Mid T}, OrientedDemand D a b → ∀ X : Set K, X.Nonempty →
      G X ≠ upset (.mid a) ∪ upset (.mid b) := by
    intro a b hd X hX he
    have ha : ¬ v (.mid a) X := by
      change Role.mid a ∈ G X
      rw [he]
      exact Or.inl (show Role.mid a ≤ .mid a from le_refl _)
    have hb : ¬ v (.mid b) X := by
      change Role.mid b ∈ G X
      rw [he]
      exact Or.inr (show Role.mid b ≤ .mid b from le_refl _)
    have hA : Forces v X (PairFormula a b) := by
      apply (forces_pair v X a b).mpr
      intro p hpa hpb
      by_contra hp
      have hpG : p ∈ G X := hp
      rw [he] at hpG
      exact hpG.elim hpa hpb
    exact (h.S a b hd X hX (Set.subset_univ _) hA).elim ha hb
  exact {
    trace := G
    nonempty := by
      intro X hX
      by_contra hn
      apply h.N X hX (Set.subset_univ _)
      apply (forces_N v X).mpr
      intro p
      by_contra hp
      exact hn ⟨p, hp⟩
    mono := by
      intro X Y hX hXY p hpX hpY
      exact hpX (hv p Y X hX hXY hpY)
    upward := up
    principalize := principal
    base_nonempty := hne
    root := hroot
    no_forbidden := by
      intro a b hd X hX
      rcases hd with hd | hd
      · exact forbidden hd X hX
      · simpa only [Set.union_comm] using forbidden hd X hX
  }

end Medvedev
