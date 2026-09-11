import Medvedev.Basic

/-!
# Definition `def:realization` and its immediate consequences

`holds A p` is the graph of the partial role function. `functional` proves
that each set has at most one role; `toPartialFunction_spec` below verifies
the equivalence with an Option-valued function. Empty sets have no role.

The H-conditions make sense without finiteness. `FiniteRealizable` at the
end restricts to positive finite carriers, as in the manuscript.
-/

namespace Medvedev

variable {T K : Type} [DecidableEq T]
/-!
This codifies the conditions H0. Basically forces for the whole set to have role r, and 
for the singletons to have the Max-roles. Back is a formalization of H1a and forth is H1b
-/
structure Realization (D : Wang T) (K : Type) where
  holds : Set K → Role T → Prop
  nonempty : ∀ {A p}, holds A p → A.Nonempty
  base : holds Set.univ .root
  singleton : ∀ k, ∃ c, holds {k} (.max c)
  back : ∀ {A p q}, holds A p → p ≤ q → ∃ B, B ⊆ A ∧ holds B q
  forth : ∀ {A B p q}, holds A p → holds B q → B ⊆ A → p ≤ q
  respond : ∀ {a b X Y}, demand D a b → holds X (.mid a) → holds Y (.mid b) →
    ∃ Z p, Z ⊆ X ∪ Y ∧ holds Z p ∧ ¬ Role.mid a ≤ p ∧ ¬ Role.mid b ≤ p

namespace Realization

variable {D : Wang T} (R : Realization D K)

theorem functional {A : Set K} {p q : Role T} (hp : R.holds A p) (hq : R.holds A q) : p = q :=
  le_antisymm (R.forth hp hq (Set.Subset.refl A)) (R.forth hq hp (Set.Subset.refl A))

noncomputable def toPartialFunction (A : Set K) : Option (Role T) := by
  classical
  exact if h : ∃ p, R.holds A p then some (Classical.choose h) else none

theorem toPartialFunction_spec (A : Set K) (p : Role T) :
    R.toPartialFunction A = some p ↔ R.holds A p := by
  classical
  unfold toPartialFunction
  split_ifs with h
  · constructor
    · intro he
      cases Option.some.inj he
      exact Classical.choose_spec h
    · intro hp
      exact congrArg some (R.functional (Classical.choose_spec h) hp)
  · simp only [false_iff]
    exact fun hp => h ⟨p, hp⟩

noncomputable def colour (k : K) : Colour T := Classical.choose (R.singleton k)

theorem colour_role (k : K) : R.holds {k} (.max (R.colour k)) := Classical.choose_spec (R.singleton k)

theorem max_colour {A : Set K} {c : Colour T} (hA : R.holds A (.max c))
    {k : K} (hk : k ∈ A) : R.colour k = c := by
  have h := R.forth hA (R.colour_role k) (Set.singleton_subset_iff.mpr hk)
  exact (max_le_max c (R.colour k)).mp h |>.symm

theorem mid_colour {A : Set K} {a : Mid T} (hA : R.holds A (.mid a))
    {k : K} (hk : k ∈ A) : R.colour k ∈ support a :=
  R.forth hA (R.colour_role k) (Set.singleton_subset_iff.mpr hk)

/-- Lemma `lem:basic-concrete` (b), including the nontrivial existence direction. -/
theorem exact_support {A : Set K} {a : Mid T} (hA : R.holds A (.mid a)) (c : Colour T) :
    (∃ k ∈ A, R.colour k = c) ↔ c ∈ support a := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact R.mid_colour hA hk
  · intro hc
    obtain ⟨B, hBA, hB⟩ := R.back (q := .max c) hA hc
    obtain ⟨k, hk⟩ := R.nonempty hB
    exact ⟨k, hBA hk, R.max_colour hB hk⟩

/-- Lemma `lem:basic-concrete` (d): no containment for incomparable roles. -/
theorem trap {A B : Set K} {p q : Role T} (hA : R.holds A p) (hB : R.holds B q)
    (h : ¬ p ≤ q) : ¬ B ⊆ A := fun hBA => h (R.forth hA hB hBA)

theorem mid_trap {A B : Set K} {a b : Mid T} (hA : R.holds A (.mid a))
    (hB : R.holds B (.mid b)) (h : a ≠ b) : ¬ B ⊆ A := R.trap hA hB h

theorem every_role (p : Role T) : ∃ A, R.holds A p := by
  obtain ⟨A, _, hA⟩ := R.back R.base (root_le p)
  exact ⟨A, hA⟩

/-- Lemma `lem:basic-concrete` (c), expressed for singleton colours. -/
theorem route {X Y Z : Set K} {c : Colour T} (hZ : Z ⊆ X ∪ Y)
    (hY : ∀ k ∈ Y, R.colour k ≠ c) {k : K} (hk : k ∈ Z) (hc : R.colour k = c) : k ∈ X := by
  rcases hZ hk with h | h
  · exact h
  · exact False.elim (hY k h hc)

end Realization

/-- All carriers in this predicate have positive finite cardinality. So the below definition works. -/
def FiniteRealizable (D : Wang T) : Prop := ∃ n : ℕ, Nonempty (Realization D (Fin (n + 1)))

end Medvedev
