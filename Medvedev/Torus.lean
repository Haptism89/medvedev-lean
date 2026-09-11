import Medvedev.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate

namespace Medvedev

variable {T : Type}

/-- Definition `def:torus`. The parameters count one less than the periods,
so both dimensions are positive by construction. `finRotate_succ_apply`
identifies the successor with modular addition by one. -/
structure TorusTiling (D : Wang T) (m n : ℕ) where
  tile : Fin (m + 1) → Fin (n + 1) → T
  horizontal : ∀ i j, D.horizontal (tile i j) (tile (finRotate (m + 1) i) j)
  vertical : ∀ i j, D.vertical (tile i j) (tile i (finRotate (n + 1) j))

def TilesTorus (D : Wang T) : Prop := ∃ m n, Nonempty (TorusTiling D m n)

/-- The finite successor argument used in Section 2; it includes the wrap edge. -/
theorem finite_cycle {A : Type} [Finite A] [Nonempty A] (f : A → A) :
    ∃ (n : ℕ) (c : Fin (n + 1) → A), ∀ i, c (finRotate (n + 1) i) = f (c i) := by
  classical
  let a : A := Classical.choice inferInstance
  obtain ⟨k, l, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] a)
  have pair : ∃ k l : ℕ, k < l ∧ f^[k] a = f^[l] a := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨k, l, h, he⟩
    · exact ⟨l, k, h, he.symm⟩
  obtain ⟨k, l, hlt, he⟩ := pair
  have hex : ∃ n : ℕ, l = k + (n + 1) := ⟨l - k - 1, by omega⟩
  obtain ⟨n, rfl⟩ := hex
  refine ⟨n, fun i => f^[k + i.val] a, ?_⟩
  intro ⟨i, hi⟩
  by_cases hil : i < n
  · rw [finRotate_of_lt hil]
    simpa only [Nat.add_assoc] using Function.iterate_succ_apply' f (k + i) a
  · have hin : i = n := by omega
    subst i
    rw [finRotate_last']
    change f^[k + 0] a = f (f^[k + n] a)
    rw [Nat.add_zero]
    calc
      f^[k] a = f^[k + (n + 1)] a := he
      _ = f (f^[k + n] a) := by
        rw [← Nat.add_assoc]
        exact Function.iterate_succ_apply' f (k + n) a

end Medvedev
