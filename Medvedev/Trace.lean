import Medvedev.Realization

namespace Medvedev

variable {T K : Type} [DecidableEq T] {D : Wang T}

def upset (p : Role T) : Set (Role T) := {q | p ≤ q}

theorem upset_injective {p q : Role T} (h : upset p = upset q) : p = q := by
  apply le_antisymm
  · have : q ∈ upset q := le_refl q
    rwa [← h] at this
  · have : p ∈ upset p := le_refl p
    rwa [h] at this

def Realization.trace (R : Realization D K) (X : Set K) : Set (Role T) :=
  {p | ∃ A, A ⊆ X ∧ R.holds A p}

theorem Realization.trace_mono (R : Realization D K) {X Y : Set K} (h : X ⊆ Y) :
    R.trace X ⊆ R.trace Y := by
  rintro p ⟨A, hA, hp⟩
  exact ⟨A, hA.trans h, hp⟩

theorem Realization.trace_nonempty (R : Realization D K) {X : Set K} (hX : X.Nonempty) :
    (R.trace X).Nonempty := by
  obtain ⟨k, hk⟩ := hX
  exact ⟨.max (R.colour k), {k}, Set.singleton_subset_iff.mpr hk, R.colour_role k⟩

theorem Realization.trace_upward (R : Realization D K) {X : Set K} {p q : Role T}
    (hp : p ∈ R.trace X) (hpq : p ≤ q) : q ∈ R.trace X := by
  obtain ⟨A, hAX, hA⟩ := hp
  obtain ⟨B, hBA, hB⟩ := R.back hA hpq
  exact ⟨B, hBA.trans hAX, hB⟩

theorem Realization.trace_principal (R : Realization D K) {A : Set K} {p : Role T}
    (hA : R.holds A p) : R.trace A = upset p := by
  ext q
  constructor
  · rintro ⟨B, hBA, hB⟩
    exact R.forth hA hB hBA
  · intro hpq
    exact R.back hA hpq

/-- Lemma `lem:forbidden-trace`, the forward implication used in recognition. -/
theorem Realization.no_forbidden_trace (R : Realization D K) {a b : Mid T}
    (hd : demand D a b) (X : Set K) : R.trace X ≠ upset (.mid a) ∪ upset (.mid b) := by
  intro he
  have ha : Role.mid a ∈ R.trace X := by
    rw [he]
    exact Or.inl (show Role.mid a ≤ .mid a from le_refl _)
  have hb : Role.mid b ∈ R.trace X := by
    rw [he]
    exact Or.inr (show Role.mid b ≤ .mid b from le_refl _)
  obtain ⟨A, hAX, hA⟩ := ha
  obtain ⟨B, hBX, hB⟩ := hb
  obtain ⟨Z, p, hZ, hp, hpa, hpb⟩ := R.respond hd hA hB
  have hx : p ∈ R.trace X := ⟨Z, hZ.trans (Set.union_subset hAX hBX), hp⟩
  rw [he] at hx
  exact hx.elim hpa hpb

/-- The trace properties recovered in Section 4. This is an intermediate
structure; the following theorem proves that its conditions suffice. -/
structure TraceModel (D : Wang T) (K : Type) where
  trace : Set K → Set (Role T)
  nonempty : ∀ {X}, X.Nonempty → (trace X).Nonempty
  mono : ∀ {X Y}, X.Nonempty → X ⊆ Y → trace X ⊆ trace Y
  upward : ∀ {X p q}, X.Nonempty → p ∈ trace X → p ≤ q → q ∈ trace X
  principalize : ∀ {X p}, X.Nonempty → p ∈ trace X →
    ∃ Y, Y.Nonempty ∧ Y ⊆ X ∧ trace Y = upset p
  base_nonempty : (Set.univ : Set K).Nonempty
  root : Role.root ∈ trace Set.univ
  no_forbidden : ∀ {a b}, demand D a b → ∀ X, X.Nonempty →
    trace X ≠ upset (.mid a) ∪ upset (.mid b)

namespace TraceModel

variable (G : TraceModel D K)

/-- Proposition `prop:recognition-cone` after recovering the trace properties. -/
def realization : Realization D K where
  holds X p := X.Nonempty ∧ G.trace X = upset p
  nonempty h := h.1
  base := by
    refine ⟨G.base_nonempty, ?_⟩
    ext p
    exact ⟨fun _ => root_le p, fun _ => G.upward G.base_nonempty G.root (root_le p)⟩
  singleton k := by
    obtain ⟨p, hp⟩ := G.nonempty (Set.singleton_nonempty k)
    obtain ⟨Y, hY, hYX, he⟩ := G.principalize (Set.singleton_nonempty k) hp
    have hYe : Y = {k} := by
      apply Set.Subset.antisymm hYX
      obtain ⟨x, hx⟩ := hY
      have heq : x = k := Set.mem_singleton_iff.mp (hYX hx)
      exact Set.singleton_subset_iff.mpr (heq ▸ hx)
    subst Y
    have maximal : ∀ q, p ≤ q → q = p := by
      intro q hpq
      have hq : q ∈ G.trace {k} := he ▸ hpq
      obtain ⟨Z, hZ, hZX, hz⟩ := G.principalize (Set.singleton_nonempty k) hq
      have hZe : Z = {k} := by
        apply Set.Subset.antisymm hZX
        obtain ⟨x, hx⟩ := hZ
        have heq : x = k := Set.mem_singleton_iff.mp (hZX hx)
        exact Set.singleton_subset_iff.mpr (heq ▸ hx)
      subst Z
      exact upset_injective (hz.symm.trans he)
    cases p with
    | root => have bad := maximal (.max (.same .h)) (root_le _); cases bad
    | mid a =>
      obtain ⟨c, hc⟩ := support_nonempty a
      have bad := maximal (.max c) hc
      cases bad
    | max c => exact ⟨c, Set.singleton_nonempty k, he⟩
  back := by
    intro X p q hX hpq
    have hq : q ∈ G.trace X := hX.2 ▸ hpq
    obtain ⟨Y, hY, hYX, he⟩ := G.principalize hX.1 hq
    exact ⟨Y, hYX, hY, he⟩
  forth := by
    intro X Y p q hX hY hYX
    have hq : q ∈ G.trace Y := hY.2 ▸ le_refl q
    have hqX := G.mono hY.1 hYX hq
    rwa [hX.2] at hqX
  respond := by
    intro a b X Y hd hX hY
    have hXY : (X ∪ Y).Nonempty := hX.1.mono Set.subset_union_left
    have hcover : upset (.mid a) ∪ upset (.mid b) ⊆ G.trace (X ∪ Y) := by
      apply Set.union_subset
      · simpa only [hX.2] using G.mono (X := X) (Y := X ∪ Y) hX.1 Set.subset_union_left
      · simpa only [hY.2] using G.mono (X := Y) (Y := X ∪ Y) hY.1 Set.subset_union_right
    have hout : ∃ p ∈ G.trace (X ∪ Y), p ∉ upset (.mid a) ∪ upset (.mid b) := by
      classical
      by_contra hn
      apply G.no_forbidden hd (X ∪ Y) hXY
      apply Set.Subset.antisymm _ hcover
      intro p hp
      by_contra hnp
      exact hn ⟨p, hp, hnp⟩
    obtain ⟨p, hp, hnot⟩ := hout
    obtain ⟨Z, hZ, hsub, he⟩ := G.principalize hXY hp
    exact ⟨Z, p, hsub, ⟨hZ, he⟩, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

end TraceModel
end Medvedev
