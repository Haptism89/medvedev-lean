import Medvedev.Semantics
import Mathlib.Data.Fintype.Pi

namespace Medvedev.Formula

variable {A K : Type} [DecidableEq A] [DecidableEq K] [Fintype K]

/-- A finite presentation of an atomic valuation. Unlisted worlds fail it. -/
abbrev FiniteValuation (A K : Type) := A → Finset (Finset K)

def FiniteForces (v : FiniteValuation A K) (X : Finset K) : Formula A → Prop
  | .atom a => X ∈ v a
  | .bot => False
  | .conj f g => FiniteForces v X f ∧ FiniteForces v X g
  | .disj f g => FiniteForces v X f ∨ FiniteForces v X g
  | .imp f g => ∀ Y : Finset K, Y.Nonempty → Y ⊆ X → FiniteForces v Y f → FiniteForces v Y g

instance finiteForcesDecidable (v : FiniteValuation A K) (X : Finset K) :
    (f : Formula A) → Decidable (FiniteForces v X f)
  | .atom a => inferInstanceAs (Decidable (X ∈ v a))
  | .bot => isFalse id
  | .conj f g => @instDecidableAnd _ _ (finiteForcesDecidable v X f) (finiteForcesDecidable v X g)
  | .disj f g => @instDecidableOr _ _ (finiteForcesDecidable v X f) (finiteForcesDecidable v X g)
  | .imp f g => by
    letI : ∀ Y : Finset K, Decidable (FiniteForces v Y f) := fun Y => finiteForcesDecidable v Y f
    letI : ∀ Y : Finset K, Decidable (FiniteForces v Y g) := fun Y => finiteForcesDecidable v Y g
    exact inferInstanceAs (Decidable (∀ Y : Finset K,
      Y.Nonempty → Y ⊆ X → FiniteForces v Y f → FiniteForces v Y g))

def FinitePersistent (v : FiniteValuation A K) : Prop :=
  ∀ a X Y, Y.Nonempty → Y ⊆ X → X ∈ v a → Y ∈ v a

instance finitePersistentDecidable [Fintype A] (v : FiniteValuation A K) :
    Decidable (FinitePersistent v) := by unfold FinitePersistent; infer_instance

/-- Exhaustive finite model checking; the search space includes every
persistent valuation on the finite atom alphabet. -/
def checkFiniteFrame [Fintype A] (f : Formula A) : Bool :=
  decide (∀ v : FiniteValuation A K, FinitePersistent v →
    ∀ X : Finset K, X.Nonempty → FiniteForces v X f)

omit [DecidableEq A] [DecidableEq K] in
theorem finiteForces_iff (v : A → Set K → Prop) (w : FiniteValuation A K)
    (bridge : ∀ (a : A) (X : Finset K), v a (X : Set K) ↔ X ∈ w a) (f : Formula A) (X : Finset K) :
    Forces v (X : Set K) f ↔ FiniteForces w X f := by
  classical
  induction f generalizing X with
  | atom a => exact bridge a X
  | bot => rfl
  | conj f g ihf ihg => exact and_congr (ihf X) (ihg X)
  | disj f g ihf ihg => exact or_congr (ihf X) (ihg X)
  | imp f g ihf ihg =>
    constructor
    · intro h Y hY hYX hf
      exact (ihg Y).mp (h (Y : Set K) (by simpa using hY)
        (by simpa using hYX) ((ihf Y).mpr hf))
    · intro h Y hY hYX hf
      have hf' : Forces v (Y.toFinset : Set K) f := by simpa using hf
      have hg' := (ihg Y.toFinset).mpr (h Y.toFinset (by simpa using hY)
        (by simpa using hYX) ((ihf Y.toFinset).mp hf'))
      simpa using hg'

/-- The finite checker is correct for the original nonempty-world semantics. -/
theorem checkFiniteFrame_iff [Fintype A] (f : Formula A) :
    checkFiniteFrame (K := K) f = true ↔ FrameValid K f := by
  classical
  simp only [checkFiniteFrame, decide_eq_true_eq]
  constructor
  · intro h v hv X hX
    let w : FiniteValuation A K := fun a => Finset.univ.filter (fun Y => v a (Y : Set K))
    have bridge : ∀ (a : A) (Y : Finset K), v a (Y : Set K) ↔ Y ∈ w a := by
      intro a Y
      simp [w]
    have hw : FinitePersistent w := by
      intro a Y Z hZ hZY ha
      apply (bridge a Z).mp
      exact hv a (Y : Set K) (Z : Set K) (by simpa using hZ) (by simpa using hZY)
        ((bridge a Y).mpr ha)
    have hf := (finiteForces_iff v w bridge f X.toFinset).mpr (h w hw X.toFinset (by simpa using hX))
    simpa using hf
  · intro h w hw X hX
    let v : A → Set K → Prop := fun a Y => Y.toFinset ∈ w a
    have bridge : ∀ (a : A) (Y : Finset K), v a (Y : Set K) ↔ Y ∈ w a := by
      intro a Y
      simp [v]
    have hv : Persistent v := by
      intro a Y Z hZ hZY ha
      exact hw a Y.toFinset Z.toFinset (by simpa using hZ) (by simpa using hZY) ha
    exact (finiteForces_iff v w bridge f X).mp (h v hv (X : Set K) (by simpa using hX))

end Medvedev.Formula
