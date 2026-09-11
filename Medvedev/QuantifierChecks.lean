import Medvedev.ReviewChecks

/-!
Quantifier audit of finite-frame semantics and recognition. These results expose
which witnesses depend on a world or carrier, and justify the one useful shift
from an existential countermodel size to a tail of countermodel sizes.
-/

namespace Medvedev.Formula

variable {A K L : Type}

/-- On a nonempty carrier, validity can be checked at the root, under every
persistent valuation. This uses persistence; it does not fix one valuation. -/
theorem frameValid_iff_root [Nonempty K] (f : Formula A) :
    FrameValid K f ↔ ∀ v : A → Set K → Prop, Persistent v → Forces v Set.univ f := by
  constructor
  · intro h v hv
    exact h v hv Set.univ Set.univ_nonempty
  · intro h v hv X hX
    exact forces_persistent hv hX (Set.subset_univ X) f (h v hv)

/-- A refutation has one valuation, chosen after the carrier size. Failure at
some world also implies failure at the root for that same valuation. -/
theorem not_inML_iff_root_countermodel (f : Formula A) :
    ¬ InML f ↔ ∃ n, ∃ v : A → Set (Fin (n + 1)) → Prop,
      Persistent v ∧ ¬ Forces v Set.univ f := by
  classical
  simp only [InML, frameValid_iff_root, not_forall, exists_prop]

/-- Surjectivity is needed to cover every target world, not just the image of
one source world. Each target world uses its own nonempty inverse image. -/
theorem frameValid_of_surjective (q : K → L) (hq : Function.Surjective q)
    (f : Formula A) (h : FrameValid K f) : FrameValid L f := by
  intro v hv X hX
  have he : q '' (q ⁻¹' X) = X := Set.image_preimage_eq X hq
  have hpre : (q ⁻¹' X).Nonempty := by
    obtain ⟨x, hx⟩ := hX
    obtain ⟨k, rfl⟩ := hq x
    exact ⟨k, hx⟩
  have hf := (forces_image q v f (q ⁻¹' X)).mp
    (h (pullValuation q v) (pull_persistent q v hv) _ hpre)
  rwa [he] at hf

/-- Validity decreases with carrier size: every larger finite carrier maps
onto a smaller one. The formula and original countermodel stay fixed. -/
theorem frameValid_antitone (f : Formula A) {n m : ℕ} (hnm : n ≤ m) :
    FrameValid (Fin (m + 1)) f → FrameValid (Fin (n + 1)) f := by
  let q : Fin (m + 1) → Fin (n + 1) := fun i =>
    if h : i.val < n + 1 then ⟨i.val, h⟩ else 0
  have hq : Function.Surjective q := by
    intro i
    refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
    simp [q, i.isLt]
  exact frameValid_of_surjective q hq f

/-- The existential size may be strengthened to a threshold because a
refutation lifts to every larger carrier. The valuation may depend on m. -/
theorem not_inML_iff_eventually_invalid (f : Formula A) :
    ¬ InML f ↔ ∃ n, ∀ m, n ≤ m → ¬ FrameValid (Fin (m + 1)) f := by
  classical
  constructor
  · intro h
    obtain ⟨n, hn⟩ := not_forall.mp h
    exact ⟨n, fun m hnm hm => hn (frameValid_antitone f hnm hm)⟩
  · rintro ⟨n, hn⟩ h
    exact hn n le_rfl (h n)

/-- Checking unboundedly many sizes is sufficient, by the proved size
monotonicity. Without that lemma this forall-exists shift would be unjustified. -/
theorem inML_iff_cofinally_valid (f : Formula A) :
    InML f ↔ ∀ N, ∃ n, N ≤ n ∧ FrameValid (Fin (n + 1)) f := by
  constructor
  · intro h N
    exact ⟨N, le_rfl, h N⟩
  · intro h N
    obtain ⟨n, hNn, hn⟩ := h N
    exact frameValid_antitone f hNn hn

end Medvedev.Formula

namespace Medvedev.QuantifierChecks

open Formula

/-- The reduction with its valuation and carrier quantifiers written out. -/
theorem correct_with_root_countermodel (c : WangCode) :
    TilesTorus c.system ↔ ∃ n, ∃ v : ℕ → Set (Fin (n + 1)) → Prop,
      Persistent v ∧ ¬ Forces v Set.univ c.formula :=
  c.correct.trans (not_inML_iff_root_countermodel c.formula)

/-- The exact manuscript corollary: once realizable, all and only carrier
sizes above one positive threshold are realizable. n indexes size n+1. -/
theorem realization_sizes_form_tail {T : Type} [DecidableEq T] (D : Wang T)
    (h : FiniteRealizable D) :
    ∃ n₀, 1 ≤ n₀ ∧ ∀ n, Nonempty (Realization D (Fin (n + 1))) ↔ n₀ ≤ n := by
  classical
  let n₀ := Nat.find h
  have hn₀ : Nonempty (Realization D (Fin (n₀ + 1))) := Nat.find_spec h
  have positive : 1 ≤ n₀ := by
    by_contra hp
    have he : n₀ = 0 := by omega
    exact Review.no_singleton_realization D (by simpa only [he] using hn₀)
  refine ⟨n₀, positive, fun n => ⟨fun hn => Nat.find_min' h hn, ?_⟩⟩
  intro hle
  let q : Fin (n + 1) → Fin (n₀ + 1) := fun i =>
    if hi : i.val < n₀ + 1 then ⟨i.val, hi⟩ else 0
  have hq : Function.Surjective q := by
    intro i
    exact ⟨⟨i.val, by have := i.isLt; omega⟩, by simp [q, i.isLt]⟩
  obtain ⟨R⟩ := hn₀
  exact ⟨R.lift q hq⟩

/-- Every world has a visible role, but no single role is visible at every
world of a realization. Thus the N-clause's forall-exists cannot be swapped. -/
theorem visible_role_depends_on_world {T K : Type} [DecidableEq T] {D : Wang T}
    (R : Realization D K) :
    (∀ X, X.Nonempty → ∃ p, p ∈ R.trace X) ∧
      ¬ (∃ p, ∀ X, X.Nonempty → p ∈ R.trace X) := by
  refine ⟨fun _ hX => R.trace_nonempty hX, ?_⟩
  rintro ⟨p, hp⟩
  obtain ⟨X, hX⟩ := R.every_role (.max (.same .h))
  obtain ⟨Y, hY⟩ := R.every_role (.max (.same .v))
  have hx := hp X (R.nonempty hX)
  have hy := hp Y (R.nonempty hY)
  rw [R.trace_principal hX] at hx
  rw [R.trace_principal hY] at hy
  cases p with
  | root => exact hx
  | mid _ => exact hx
  | max c =>
    have hh : Colour.same Axis.h = c := hx
    have hv : Colour.same Axis.v = c := hy
    cases hh.trans hv.symm

/-- Every recognizing formula is valid on the one-point carrier. In
particular, existential invalidity cannot mean invalidity on every size. -/
theorem recognizing_formula_valid_on_singleton (c : WangCode) :
    FrameValid (Fin 1) c.formula := by
  classical
  have h : FrameValid (Fin 1) (alpha c.system) := by
    by_contra h
    exact Review.no_singleton_realization c.system ((recognition c.system).mp h)
  exact (frameValid_rename_iff Encodable.encode Encodable.encode_injective _).mpr h

/-- A persistent valuation with different truth values on the two singleton
worlds. Its value at an atom is independent of the atom's name. -/
def splitValuation (_ : ℕ) (X : Set Bool) : Prop := X ⊆ {false}

theorem splitValuation_persistent : Persistent splitValuation :=
  fun _ _ _ _ hYX hX => hYX.trans hX

/-- An implication can fail only at a strict successor: its antecedent is
false at the root, so replacing the existential successor by the root fails. -/
theorem implication_witness_cannot_be_fixed_to_root :
    ¬ Forces splitValuation Set.univ (.atom 0) ∧
      ¬ Forces splitValuation Set.univ (.imp (.atom 0) .bot) := by
  constructor
  · intro h
    have bad := h (Set.mem_univ true)
    cases bad
  · intro h
    exact h {false} (Set.singleton_nonempty false) (Set.subset_univ _)
      (Set.Subset.refl _)

/-- Failure at some world is not failure at every world, even for a fixed
persistent valuation. Excluded middle holds at both singleton successors. -/
theorem refutation_does_not_mean_failure_everywhere :
    let f : Formula ℕ := .disj (.atom 0) (.imp (.atom 0) .bot)
    ¬ Forces splitValuation Set.univ f ∧
      ∀ k : Bool, Forces splitValuation {k} f := by
  dsimp only
  refine ⟨fun h => h.elim implication_witness_cannot_be_fixed_to_root.1
    implication_witness_cannot_be_fixed_to_root.2, ?_⟩
  intro k
  cases k with
  | false => exact Or.inl (Set.Subset.refl _)
  | true =>
    right
    intro Y hY hYtrue hYfalse
    obtain ⟨b, hb⟩ := hY
    have ht : b = true := Set.mem_singleton_iff.mp (hYtrue hb)
    have hf : b = false := Set.mem_singleton_iff.mp (hYfalse hb)
    cases ht.symm.trans hf

end Medvedev.QuantifierChecks
