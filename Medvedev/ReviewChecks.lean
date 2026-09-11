import Medvedev.Reduction
import Medvedev.UpperBound

/-!
# Adversarial definition checks

These checks expose two representation changes explicitly: worlds as a subtype
of nonempty sets (paper lines 100--105, 1547--1582), and roles as an actual
partial function (paper lines 389--418). They also distinguish conventions
whose accidental reversal would substantially change the mathematics.
-/

namespace Medvedev.Review

open Formula

variable {A K T : Type}

abbrev World (K : Type) := {X : Set K // X.Nonempty}

def WorldPersistent (v : A → World K → Prop) : Prop :=
  ∀ a X Y, Y.val ⊆ X.val → v a X → v a Y

def WorldForces (v : A → World K → Prop) (X : World K) : Formula A → Prop
  | .atom a => v a X
  | .bot => False
  | .conj f g => WorldForces v X f ∧ WorldForces v X g
  | .disj f g => WorldForces v X f ∨ WorldForces v X g
  | .imp f g => ∀ Y : World K, Y.val ⊆ X.val → WorldForces v Y f → WorldForces v Y g

def WorldValid (K : Type) (f : Formula A) : Prop :=
  ∀ v : A → World K → Prop, WorldPersistent v → ∀ X, WorldForces v X f

theorem forces_world_iff (v : A → Set K → Prop) (X : World K) (f : Formula A) :
    Forces v X.val f ↔ WorldForces (fun a Y => v a Y.val) X f := by
  induction f generalizing X with
  | atom a => rfl
  | bot => rfl
  | conj f g ihf ihg => exact and_congr (ihf X) (ihg X)
  | disj f g ihf ihg => exact or_congr (ihf X) (ihg X)
  | imp f g ihf ihg =>
    constructor
    · intro h Y hYX hf
      exact (ihg Y).mp (h Y.val Y.property hYX ((ihf Y).mpr hf))
    · intro h Y hY hYX hf
      exact (ihg ⟨Y, hY⟩).mpr (h ⟨Y, hY⟩ hYX ((ihf ⟨Y, hY⟩).mp hf))

/-- Adding arbitrary values at the empty set does not change frame validity. -/
theorem frameValid_iff_worldValid (f : Formula A) : FrameValid K f ↔ WorldValid K f := by
  classical
  constructor
  · intro h v hv X
    let w : A → Set K → Prop := fun a Y => ∃ hY : Y.Nonempty, v a ⟨Y, hY⟩
    have hw : Persistent w := by
      rintro a Y Z hZ hZY ⟨hY, ha⟩
      exact ⟨hZ, hv a ⟨Y, hY⟩ ⟨Z, hZ⟩ hZY ha⟩
    have he : (fun a (Y : World K) => w a Y.val) = v := by
      funext a Y
      apply propext
      exact ⟨fun ⟨_, ha⟩ => ha, fun ha => ⟨Y.property, ha⟩⟩
    have hf := (forces_world_iff w X f).mp (h w hw X.val X.property)
    rwa [he] at hf
  · intro h v hv X hX
    apply (forces_world_iff v ⟨X, hX⟩ f).mpr
    exact h (fun a Y => v a Y.val)
      (fun a Y Z hZY => hv a Y.val Z.val Z.property hZY) ⟨X, hX⟩

/-- The final reduction with the paper's nonempty-world domain in its conclusion. -/
theorem correct_on_paper_worlds (c : WangCode) :
    TilesTorus c.system ↔ ¬ (∀ n : ℕ, WorldValid (Fin (n + 1)) c.formula) := by
  have he : InML c.formula ↔ ∀ n : ℕ, WorldValid (Fin (n + 1)) c.formula :=
    forall_congr' (fun _ => frameValid_iff_worldValid c.formula)
  exact c.correct.trans (not_congr he)

variable [DecidableEq T]

/-- A literal Option-valued version of H0, H1(a), H1(b), and H2.
The nonempty-domain condition also rules out assigning a role to the empty set. -/
structure PartialConditions (D : Wang T) (f : Set K → Option (Role T)) : Prop where
  domain : ∀ X p, f X = some p → X.Nonempty
  base : f Set.univ = some .root
  singleton : ∀ k, ∃ c, f {k} = some (.max c)
  back : ∀ X p q, f X = some p → p ≤ q → ∃ Y, Y ⊆ X ∧ f Y = some q
  forth : ∀ X Y p q, f X = some p → f Y = some q → Y ⊆ X → p ≤ q
  response : ∀ a b X Y, demand D a b → f X = some (.mid a) → f Y = some (.mid b) →
    ∃ Z p, Z ⊆ X ∪ Y ∧ f Z = some p ∧ p ∉ upset (.mid a) ∪ upset (.mid b)

theorem realization_iff_partialConditions (D : Wang T) :
    Nonempty (Realization D K) ↔ ∃ f : Set K → Option (Role T), PartialConditions D f := by
  constructor
  · rintro ⟨R⟩
    refine ⟨R.toPartialFunction, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X p hp
      exact R.nonempty ((R.toPartialFunction_spec X p).mp hp)
    · exact (R.toPartialFunction_spec _ _).mpr R.base
    · intro k
      obtain ⟨c, hc⟩ := R.singleton k
      exact ⟨c, (R.toPartialFunction_spec _ _).mpr hc⟩
    · intro X p q hp hpq
      obtain ⟨Y, hYX, hY⟩ := R.back ((R.toPartialFunction_spec _ _).mp hp) hpq
      exact ⟨Y, hYX, (R.toPartialFunction_spec _ _).mpr hY⟩
    · intro X Y p q hp hq hYX
      exact R.forth ((R.toPartialFunction_spec _ _).mp hp)
        ((R.toPartialFunction_spec _ _).mp hq) hYX
    · intro a b X Y hd hX hY
      obtain ⟨Z, p, hZ, hp, ha, hb⟩ := R.respond hd
        ((R.toPartialFunction_spec _ _).mp hX) ((R.toPartialFunction_spec _ _).mp hY)
      exact ⟨Z, p, hZ, (R.toPartialFunction_spec _ _).mpr hp, fun h => h.elim ha hb⟩
  · rintro ⟨f, h⟩
    exact ⟨{
      holds := fun X p => f X = some p
      nonempty := fun hp => h.domain _ _ hp
      base := h.base
      singleton := h.singleton
      back := fun hp hpq => h.back _ _ _ hp hpq
      forth := fun hp hq hYX => h.forth _ _ _ _ hp hq hYX
      respond := by
        intro a b X Y hd hX hY
        obtain ⟨Z, p, hZ, hp, hout⟩ := h.response a b X Y hd hX hY
        exact ⟨Z, p, hZ, hp, fun ha => hout (Or.inl ha), fun hb => hout (Or.inr hb)⟩
    }⟩

/-- H0 is incompatible with a singleton carrier; it cannot yield a spurious tiling. -/
theorem no_singleton_realization (D : Wang T) : ¬ Nonempty (Realization D (Fin 1)) := by
  rintro ⟨R⟩
  obtain ⟨c, hc⟩ := R.singleton 0
  have he : (Set.univ : Set (Fin 1)) = {0} := by ext k; simp [Subsingleton.elim k 0]
  rw [← he] at hc
  have bad := R.functional R.base hc
  cases bad

/-- A directed compatibility test: swapping source and target changes D6. -/
def directedThree : Wang (Fin 3) where
  horizontal t u := u = finRotate 3 t
  vertical t u := t = u

theorem forward_horizontal_pair_is_allowed : ¬ demandCode directedThree (.expected .h 0) (.candidate .h 1) := by
  change ¬ (Axis.h = Axis.h ∧ ¬ (1 : Fin 3) = finRotate 3 0)
  decide
theorem reverse_horizontal_pair_is_forbidden : demandCode directedThree (.expected .h 1) (.candidate .h 0) := by
  change Axis.h = Axis.h ∧ ¬ (0 : Fin 3) = finRotate 3 1
  decide

/-- Unused tile types still have expected representatives with their own label. -/
theorem unused_seed_expected_role : Compressed.stateRole (fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 2))
    (.expected .h (.seed 1)) = .expected .h 1 := rfl

-- On a one-by-one torus, this point fills the candidate's missing next-column
-- marker. Replacing the expected seed's opposite-axis block by x₀ breaks this.
theorem opposite_axis_seed_witness :
    let τ := fun (_ : Fin 1) (_ : Fin 1) => (0 : Fin 2)
    let p : Compressed.Marker (Fin 1) (Fin 1) (Fin 2) × Colour (Fin 2) := (.x 0, .next .h)
    p ∈ Compressed.representative τ id id 0 0 (.expected .h (.seed 1)) ∧
    p ∉ Compressed.representative τ id id 0 0 (.candidate .h (.actual 0 0)) := by
  simp [Compressed.representative, Compressed.stateRole, support, Compressed.blocks,
    Compressed.cellBlocks, Compressed.tile]

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- Excluded middle holds on one singleton world, and fails on the branching F₂.
theorem excluded_middle_singleton : checkFrame (.disj (.atom 0) (.imp (.atom 0) .bot)) 0 = true := by decide
theorem excluded_middle_two_points : checkFrame (.disj (.atom 0) (.imp (.atom 0) .bot)) 1 = false := by decide
-- The implication includes the present world itself, even when it is a singleton.
theorem implication_checks_current_world : checkFrame (.imp Formula.top .bot) 0 = false := by decide
-- Atom-free formulas exercise the empty alphabet of the finite checker.
theorem atom_free_top : checkFrame (Formula.top : Formula ℕ) 1 = true := by decide

end Medvedev.Review
