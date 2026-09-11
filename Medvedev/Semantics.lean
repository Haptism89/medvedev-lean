import Medvedev.Basic
import Mathlib.Data.Finset.Sort

namespace Medvedev

inductive Formula (Atom : Type) where
  | atom : Atom → Formula Atom
  | bot : Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

namespace Formula

variable {Atom K : Type}

def top : Formula Atom := .imp .bot .bot

/-- The domain includes empty sets for convenience, but implication only
quantifies over nonempty subsets; validity below only quantifies over
nonempty worlds. In particular, bottom is never forced at a world. -/
def Forces (v : Atom → Set K → Prop) (X : Set K) : Formula Atom → Prop
  | .atom p => v p X
  | .bot => False
  | .conj f g => Forces v X f ∧ Forces v X g
  | .disj f g => Forces v X f ∨ Forces v X g
  | .imp f g => ∀ Y : Set K, Y.Nonempty → Y ⊆ X → Forces v Y f → Forces v Y g

def Persistent (v : Atom → Set K → Prop) : Prop :=
  ∀ p X Y, Y.Nonempty → Y ⊆ X → v p X → v p Y

theorem forces_persistent {v : Atom → Set K → Prop} (hv : Persistent v)
    {X Y : Set K} (hY : Y.Nonempty) (hYX : Y ⊆ X) (f : Formula Atom) :
    Forces v X f → Forces v Y f := by
  induction f with
  | atom p => exact hv p X Y hY hYX
  | bot => exact id
  | conj f g hf hg => exact fun h => ⟨hf h.1, hg h.2⟩
  | disj f g hf hg => exact fun h => h.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hg h))
  | imp f g _ _ => exact fun h Z hZ hZY => h Z hZ (hZY.trans hYX)

/-- Equation `eq:failure-implication`, including the nonempty witness. -/
theorem not_forces_imp (v : Atom → Set K → Prop) (X : Set K) (f g : Formula Atom) :
    ¬ Forces v X (.imp f g) ↔
      ∃ Y : Set K, Y.Nonempty ∧ Y ⊆ X ∧ Forces v Y f ∧ ¬ Forces v Y g := by
  classical
  simp only [Forces, not_forall, exists_prop]

def all (l : List (Formula Atom)) : Formula Atom := l.foldr .conj top

@[simp] theorem forces_top (v : Atom → Set K → Prop) (X : Set K) : Forces v X top :=
  fun _ _ _ h => h

theorem forces_all (v : Atom → Set K → Prop) (X : Set K) (l : List (Formula Atom)) :
    Forces v X (all l) ↔ ∀ f ∈ l, Forces v X f := by
  induction l with
  | nil => simp [all, top, Forces]
  | cons f l ih => simpa [all, Forces] using and_congr Iff.rfl ih

def allFinset {A : Type} [Encodable A] (s : Finset A) (f : A → Formula Atom) : Formula Atom :=
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  all ((s.sort (· ≤ ·)).map f)

@[simp] theorem forces_allFinset {A : Type} [Encodable A] (s : Finset A) (f : A → Formula Atom)
    (v : Atom → Set K → Prop) (X : Set K) :
    Forces v X (allFinset s f) ↔ ∀ a ∈ s, Forces v X (f a) := by
  simp [allFinset, forces_all]

/-- Validity on the reverse-inclusion frame of nonempty subsets of K. -/
def FrameValid (K : Type) (f : Formula Atom) : Prop :=
  ∀ v : Atom → Set K → Prop, Persistent v → ∀ X, X.Nonempty → Forces v X f

def InML (f : Formula Atom) : Prop := ∀ n : ℕ, FrameValid (Fin (n + 1)) f

end Formula
end Medvedev
