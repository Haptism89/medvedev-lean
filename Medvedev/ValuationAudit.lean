import Medvedev.UpperBound

/-!
The manuscript distinguishes all persistent valuations (Medvedev validity)
from flat atomic valuations (the inquisitive corollary). This difference is
substantive: double-negation elimination separates them already on two points.
These definitions and proofs use the original forcing clauses directly.
-/

namespace Medvedev.ValuationAudit

open Formula

variable {A K : Type}

def flat (truth : A → Set K) : A → Set K → Prop := fun a X => X ⊆ truth a

theorem flat_persistent (truth : A → Set K) : Persistent (flat truth) := by
  intro a X Y _ hYX hX
  exact hYX.trans hX

def doubleNegation (a : A) : Formula A :=
  .imp (.imp (.imp (.atom a) .bot) .bot) (.atom a)

/-- Flat atomic truth is stable under double negation, on every carrier. -/
theorem flat_doubleNegation (truth : A → Set K) (a : A) (X : Set K) :
    Forces (flat truth) X (doubleNegation a) := by
  classical
  intro Y _ _ hnn y hy
  by_contra hnot
  apply hnn {y} (Set.singleton_nonempty y) (Set.singleton_subset_iff.mpr hy)
  intro Z hZ hZY hZtruth
  obtain ⟨z, hz⟩ := hZ
  have hzy : z = y := Set.mem_singleton_iff.mp (hZY hz)
  exact hnot (hzy ▸ hZtruth hz)

/-- This is a persistent valuation, but it is not flat on a two-point carrier. -/
def singletonTruth : ℕ → Set K → Prop := fun _ X => X.Subsingleton

theorem singletonTruth_persistent : Persistent (singletonTruth (K := K)) := by
  intro _ X Y _ hYX hX x hx y hy
  exact hX (hYX hx) (hYX hy)

theorem singletonTruth_not_flat :
    ¬ ∃ truth : ℕ → Set Bool, singletonTruth = flat truth := by
  rintro ⟨truth, he⟩
  have hf : false ∈ truth 0 := by
    have h : singletonTruth 0 ({false} : Set Bool) := Set.subsingleton_singleton
    rw [he] at h
    exact h (Set.mem_singleton false)
  have ht : true ∈ truth 0 := by
    have h : singletonTruth 0 ({true} : Set Bool) := Set.subsingleton_singleton
    rw [he] at h
    exact h (Set.mem_singleton true)
  have hroot : flat truth 0 Set.univ := by
    intro b _
    cases b <;> assumption
  rw [← he] at hroot
  exact Bool.false_ne_true (hroot (Set.mem_univ false) (Set.mem_univ true))

theorem two_point_doubleNegation_failure :
    ¬ Forces (singletonTruth (K := Fin 2)) Set.univ (doubleNegation 0) := by
  intro h
  have hnn : Forces (singletonTruth (K := Fin 2)) Set.univ
      (.imp (.imp (.atom 0) .bot) .bot) := by
    intro Y hY _ hn
    obtain ⟨y, hy⟩ := hY
    exact hn {y} (Set.singleton_nonempty y) (Set.singleton_subset_iff.mpr hy)
      Set.subsingleton_singleton
  have hroot := h Set.univ ⟨0, Set.mem_univ 0⟩ (Set.Subset.refl _) hnn
  have he : (0 : Fin 2) = 1 := hroot (Set.mem_univ 0) (Set.mem_univ 1)
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-- All flat valuations validate this formula, yet actual Medvedev validity fails.
Replacing the valuation quantifier by flat valuations would change the theorem. -/
theorem flat_valid_but_not_inML :
    (∀ n (truth : ℕ → Set (Fin (n + 1))) X, X.Nonempty →
      Forces (flat truth) X (doubleNegation 0)) ∧ ¬ InML (doubleNegation 0) := by
  refine ⟨fun _ truth X _ => flat_doubleNegation truth 0 X, ?_⟩
  intro h
  exact two_point_doubleNegation_failure
    (h 1 singletonTruth singletonTruth_persistent Set.univ ⟨0, Set.mem_univ 0⟩)

theorem actual_checker_rejects_doubleNegation : checkFrame (doubleNegation 0) 1 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact two_point_doubleNegation_failure
    ((checkFrame_iff _ _).mp h singletonTruth singletonTruth_persistent Set.univ
      ⟨0, Set.mem_univ 0⟩)

end Medvedev.ValuationAudit
