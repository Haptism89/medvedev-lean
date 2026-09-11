import Medvedev.Realization

namespace Medvedev

variable {T K S : Type} [DecidableEq T]

/-- Explicit obligations for assigning roles to a family of concrete representatives. -/
structure RepresentativeData (D : Wang T) (K S : Type) where
  colour : K → Colour T
  colour_surjective : Function.Surjective colour
  label : S → Mid T
  label_surjective : Function.Surjective label
  set : S → Set K
  set_nontrivial : ∀ s, (set s).Nontrivial
  set_proper : ∀ s, ¬ Set.univ ⊆ set s
  exact_support : ∀ s c, (∃ k ∈ set s, colour k = c) ↔ c ∈ support (label s)
  separation : ∀ s t, set s ⊆ set t → label s = label t
  response : ∀ s t, demand D (label s) (label t) →
    ∃ u, set u ⊆ set s ∪ set t ∧ label u ≠ label s ∧ label u ≠ label t

namespace RepresentativeData

variable {D : Wang T} (A : RepresentativeData D K S)

inductive Assigned : Set K → Role T → Prop
  | base : Assigned Set.univ .root
  | singleton (k : K) : Assigned {k} (.max (A.colour k))
  | representative (s : S) : Assigned (A.set s) (.mid (A.label s))

theorem no_subset_singleton (s : S) (k : K) : ¬ A.set s ⊆ {k} := by
  obtain ⟨x, hx, y, hy, hxy⟩ := A.set_nontrivial s
  intro h
  exact hxy ((Set.mem_singleton_iff.mp (h hx)).trans (Set.mem_singleton_iff.mp (h hy)).symm)

include A in
theorem univ_no_subset_singleton (k : K) : ¬ Set.univ ⊆ ({k} : Set K) := by
  obtain ⟨x, hx⟩ := A.colour_surjective (.same .h)
  obtain ⟨y, hy⟩ := A.colour_surjective (.same .v)
  intro h
  have hxy : x = y := (Set.mem_singleton_iff.mp (h (Set.mem_univ x))).trans
    (Set.mem_singleton_iff.mp (h (Set.mem_univ y))).symm
  have : (Colour.same .h : Colour T) = .same .v := hx.symm.trans ((congrArg A.colour hxy).trans hy)
  cases this

/-- Proposition `prop:compressed-roles`, plus H2 when its explicit response
obligation has been proved. The obligations are discharged for the actual
blocklists in the compressed-construction modules. -/
def realization : Realization D K where
  holds := A.Assigned
  nonempty := by
    intro X p h
    cases h with
    | base =>
      obtain ⟨k, _⟩ := A.colour_surjective (.same .h)
      exact ⟨k, Set.mem_univ _⟩
    | singleton k => exact Set.singleton_nonempty k
    | representative s => exact (A.set_nontrivial s).nonempty
  base := Assigned.base
  singleton k := ⟨A.colour k, Assigned.singleton k⟩
  back := by
    intro X p q hX hpq
    cases hX with
    | base =>
      cases q with
      | root => exact ⟨Set.univ, Set.Subset.refl _, Assigned.base⟩
      | mid a =>
        obtain ⟨s, rfl⟩ := A.label_surjective a
        exact ⟨A.set s, Set.subset_univ _, Assigned.representative s⟩
      | max c =>
        obtain ⟨k, rfl⟩ := A.colour_surjective c
        exact ⟨{k}, Set.subset_univ _, Assigned.singleton k⟩
    | singleton k =>
      cases q with
      | root => exact False.elim hpq
      | mid _ => exact False.elim hpq
      | max c =>
        have he : A.colour k = c := hpq
        subst c
        exact ⟨{k}, Set.Subset.refl _, Assigned.singleton k⟩
    | representative s =>
      cases q with
      | root => exact False.elim hpq
      | mid a =>
        have he : A.label s = a := hpq
        subst a
        exact ⟨A.set s, Set.Subset.refl _, Assigned.representative s⟩
      | max c =>
        obtain ⟨k, hk, rfl⟩ := (A.exact_support s c).mpr hpq
        exact ⟨{k}, Set.singleton_subset_iff.mpr hk, Assigned.singleton k⟩
  forth := by
    intro X Y p q hX hY hsub
    cases hX with
    | base => exact root_le q
    | singleton k =>
      cases hY with
      | base => exact False.elim (A.univ_no_subset_singleton k hsub)
      | singleton l =>
        have hlk : l = k := Set.mem_singleton_iff.mp (hsub (Set.mem_singleton l))
        subst l
        exact le_refl _
      | representative s => exact False.elim (A.no_subset_singleton s k hsub)
    | representative s =>
      cases hY with
      | base => exact False.elim (A.set_proper s hsub)
      | singleton k =>
        exact (A.exact_support s (A.colour k)).mp
          ⟨k, hsub (Set.mem_singleton k), rfl⟩
      | representative t => exact (A.separation t s hsub).symm
  respond := by
    intro a b X Y hd hX hY
    cases hX with
    | representative s =>
      cases hY with
      | representative t =>
        obtain ⟨u, hsub, hus, hut⟩ := A.response s t hd
        exact ⟨A.set u, .mid (A.label u), hsub, Assigned.representative u, Ne.symm hus, Ne.symm hut⟩

end RepresentativeData
end Medvedev
