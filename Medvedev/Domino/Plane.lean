import Medvedev.Domino.Periodic

namespace Medvedev.Domino

/-- The paper's plane uses all integer coordinates, including negative ones. -/
structure PlaneTiling {T : Type} (D : Wang T) where
  tile : ℤ → ℤ → T
  horizontal : ∀ i j, D.horizontal (tile i j) (tile (i + 1) j)
  vertical : ∀ i j, D.vertical (tile i j) (tile i (j + 1))

/-- Jeandel's common positive horizontal and vertical period. -/
def PlaneTiling.Periodic {T : Type} {D : Wang T} (c : PlaneTiling D) : Prop :=
  ∃ p : ℕ, 0 < p ∧ (∀ i j, c.tile (i + p) j = c.tile i j) ∧
    (∀ i j, c.tile i (j + p) = c.tile i j)

def intIndex (n : ℕ) (z : ℤ) : Fin (n + 1) :=
  ⟨(z % (n + 1)).toNat, by
    have := Int.emod_nonneg z (show (n : ℤ) + 1 ≠ 0 by omega)
    have := Int.emod_lt_of_pos z (show (0 : ℤ) < n + 1 by omega)
    omega⟩

@[simp] theorem intIndex_nat (n i : ℕ) : intIndex n i = index n i := by
  apply Fin.ext
  change ((i : ℤ) % ((n + 1 : ℕ) : ℤ)).toNat = i % (n + 1)
  rw [← Int.natCast_emod, Int.toNat_natCast]

theorem intIndex_succ (n : ℕ) (z : ℤ) :
    intIndex n (z + 1) = finRotate (n + 1) (intIndex n z) := by
  have h : (((z % (n + 1)).toNat : ℕ) : ℤ) = z % (n + 1) :=
    Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))
  calc
    intIndex n (z + 1) = intIndex n (((z % (n + 1)).toNat : ℤ) + 1) := by
      apply Fin.ext
      simp only [intIndex, h]
      rw [Int.add_emod, Int.add_emod (z % _) 1]
      simp
    _ = index n ((z % (n + 1)).toNat + 1) := by
      rw [← Int.natCast_one, ← Int.natCast_add, intIndex_nat]
    _ = finRotate (n + 1) (index n (z % (n + 1)).toNat) := index_succ _ _
    _ = finRotate (n + 1) (intIndex n z) := by
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt (intIndex n z).isLt

def TorusTiling.plane {T : Type} {D : Wang T} {m n : ℕ}
    (c : Medvedev.TorusTiling D m n) : PlaneTiling D where
  tile i j := c.tile (intIndex m i) (intIndex n j)
  horizontal i j := by simpa only [intIndex_succ] using c.horizontal (intIndex m i) (intIndex n j)
  vertical i j := by simpa only [intIndex_succ] using c.vertical (intIndex m i) (intIndex n j)

theorem TorusTiling.plane_periodic {T : Type} {D : Wang T} {m n : ℕ}
    (c : Medvedev.TorusTiling D m n) : (TorusTiling.plane c).Periodic := by
  refine ⟨(m + 1) * (n + 1), Nat.mul_pos (by omega) (by omega), ?_, ?_⟩
  · intro i j
    change c.tile _ _ = c.tile _ _
    congr 1
    apply Fin.ext
    simp [intIndex, Int.natCast_mul, Int.natCast_add, Int.add_mul_emod_self_left]
  · intro i j
    change c.tile _ _ = c.tile _ _
    congr 1
    apply Fin.ext
    simp [intIndex, Int.natCast_mul, Int.natCast_add, Int.add_mul_emod_self_right]

theorem tilesTorus_of_periodic_plane {T : Type} {D : Wang T}
    (c : PlaneTiling D) (h : c.Periodic) : TilesTorus D := by
  obtain ⟨p, hp, hh, hv⟩ := h
  cases p with
  | zero => omega
  | succ p =>
    refine ⟨p, p, ⟨⟨fun i j => c.tile i.val j.val, ?_, ?_⟩⟩⟩
    · intro i j
      by_cases hi : i.val < p
      · simpa [finRotate_of_lt hi] using c.horizontal i.val j.val
      · have he : i = Fin.last p := Fin.ext (by simp; omega)
        subst i
        have h := c.horizontal p j.val
        have hwrap := hh 0 j.val
        simpa [finRotate_last, ← hwrap] using h
    · intro i j
      by_cases hj : j.val < p
      · simpa [finRotate_of_lt hj] using c.vertical i.val j.val
      · have he : j = Fin.last p := Fin.ext (by simp; omega)
        subst j
        have h := c.vertical i.val p
        have hwrap := hv i.val 0
        simpa [finRotate_last, ← hwrap] using h

theorem tilesTorus_iff_periodic_plane {T : Type} (D : Wang T) :
    TilesTorus D ↔ ∃ c : PlaneTiling D, c.Periodic := by
  constructor
  · rintro ⟨m, n, ⟨c⟩⟩
    exact ⟨TorusTiling.plane c, TorusTiling.plane_periodic c⟩
  · rintro ⟨c, hc⟩
    exact tilesTorus_of_periodic_plane c hc

end Medvedev.Domino
