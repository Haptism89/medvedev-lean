import Medvedev.Domino.ArithmeticBackground
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

namespace Medvedev.Domino.ArithmeticBackground

/-- Multiplying by 2 and dividing by 3 cannot return a positive integer to
itself in a positive number of steps. -/
theorem no_positive_scale_cycle (s : ℕ → ℕ) (hs : 0 < s 0)
    (step : ∀ i, s (i + 1) = 2 * s i ∨ 3 * s (i + 1) = s i)
    (n : ℕ) (hn : 0 < n) (close : s n = s 0) : False := by
  have chain : ∀ k, ∃ a b : ℕ, a + b = k ∧ 3 ^ b * s k = 2 ^ a * s 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, 0, rfl, by simp⟩
    | succ k ih =>
      obtain ⟨a, b, hab, he⟩ := ih
      rcases step k with hd | ht
      · refine ⟨a + 1, b, by omega, ?_⟩
        calc
          3 ^ b * s (k + 1) = 2 * (3 ^ b * s k) := by rw [hd]; ring
          _ = 2 * (2 ^ a * s 0) := by rw [he]
          _ = 2 ^ (a + 1) * s 0 := by rw [pow_succ]; ring
      · refine ⟨a, b + 1, by omega, ?_⟩
        calc
          3 ^ (b + 1) * s (k + 1) = 3 ^ b * (3 * s (k + 1)) := by rw [pow_succ]; ring
          _ = 3 ^ b * s k := by rw [ht]
          _ = 2 ^ a * s 0 := he
  obtain ⟨a, b, hab, he⟩ := chain n
  rw [close] at he
  have hp : 3 ^ b = 2 ^ a := Nat.eq_of_mul_eq_mul_right hs he
  have hc : Nat.Coprime (2 ^ a) (3 ^ b) := (by decide : Nat.Coprime 2 3).pow a b
  rw [hp] at hc
  have ha : 2 ^ a = 1 := by simpa using hc
  have hb : 3 ^ b = 1 := hp.trans ha
  have az : a = 0 := by
    cases a with
    | zero => rfl
    | succ a => simp [pow_succ] at ha
  have bz : b = 0 := by
    cases b with
    | zero => rfl
    | succ b => simp [pow_succ] at hb
  omega

open scoped BigOperators

def mass {m n : ℕ} (c : Medvedev.TorusTiling system m n) (j : Fin (n + 1)) : ℕ :=
  ∑ i, ((c.tile i j).val.south.val + 1)

theorem mass_pos {m n : ℕ} (c : Medvedev.TorusTiling system m n) (j : Fin (n + 1)) :
    0 < mass c j := by
  unfold mass
  rw [Fin.sum_univ_succ]
  omega

theorem row_mode {m n : ℕ} (c : Medvedev.TorusTiling system m n)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (c.tile i j).val.double = (c.tile 0 j).val.double := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := (c.horizontal i.castSucc j).1
    have hr : finRotate (m + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [hr] at h
    exact h.symm.trans ih

/-- Summing the local balance equations cancels every horizontal carry,
including the carry across the wrap edge. -/
theorem mass_step {m n : ℕ} (c : Medvedev.TorusTiling system m n) (j : Fin (n + 1)) :
    denominator (c.tile 0 j).val.double * mass c (finRotate (n + 1) j) =
      numerator (c.tile 0 j).val.double * mass c j := by
  have hs := congrArg (fun f : Fin (m + 1) → ℕ => ∑ i, f i)
    (funext fun i => (c.tile i j).property)
  change (∑ i, (denominator (c.tile i j).val.double * ((c.tile i j).val.north.val + 1) +
      (c.tile i j).val.east.val)) =
    ∑ i, (numerator (c.tile i j).val.double * ((c.tile i j).val.south.val + 1) +
      (c.tile i j).val.west.val) at hs
  simp_rw [row_mode c _ j] at hs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hs
  have hcarry : (∑ i, (c.tile i j).val.east.val) = ∑ i, (c.tile i j).val.west.val := by
    calc
      (∑ i, (c.tile i j).val.east.val) =
          ∑ i, (c.tile (finRotate (m + 1) i) j).val.west.val := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg Fin.val (c.horizontal i j).2
      _ = ∑ i, (c.tile i j).val.west.val :=
        Equiv.sum_comp (finRotate (m + 1)) (fun i => (c.tile i j).val.west.val)
  have hnorth : (∑ i, ((c.tile i j).val.north.val + 1)) = mass c (finRotate (n + 1) j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [c.vertical i j]
  rw [hcarry, hnorth] at hs
  exact Nat.add_right_cancel hs

/-- The fixed background has no periodic torus tiling of any positive size. -/
theorem no_torus : ¬ TilesTorus system := by
  rintro ⟨m, n, ⟨c⟩⟩
  apply no_positive_scale_cycle (fun j => mass c (index n j))
    (mass_pos c (index n 0))
  · intro j
    have h := mass_step c (index n j)
    rw [← index_succ] at h
    cases hm : (c.tile 0 (index n j)).val.double with
    | false => exact Or.inr (by simpa [hm, numerator, denominator] using h)
    | true => exact Or.inl (by simpa [hm, numerator, denominator] using h)
  · exact Nat.zero_lt_succ n
  · congr 1
    apply Fin.ext
    simp

end Medvedev.Domino.ArithmeticBackground
