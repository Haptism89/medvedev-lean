import Medvedev.Adjacency
import Medvedev.Torus

namespace Medvedev

variable {T K : Type} [DecidableEq T] {D : Wang T}

namespace Realization

structure CoordinateCycle (R : Realization D K) (ax : Axis) (n : ℕ) where
  position : Fin (n + 1) → Set K
  separator : Fin (n + 1) → Set K
  position_role : ∀ i, R.holds (position i) (.mid (.pos ax))
  separator_role : ∀ i, R.holds (separator i) (.mid (.sep ax))
  same_part : ∀ i, R.PartIn (separator i) (.same ax) (position i)
  next_part : ∀ i, R.PartIn (position (finRotate (n + 1) i)) (.next ax) (separator i)

/-- The cyclic coordinate selection, with no assumption that selected
sets are disjoint and with a checked wrap-around edge. -/
theorem coordinate_cycle [Fintype K] (R : Realization D K) (ax : Axis) :
    ∃ n, Nonempty (CoordinateCycle R ax n) := by
  classical
  obtain ⟨N, hN⟩ := R.every_role (.mid (.notNext ax))
  obtain ⟨S, hS⟩ := R.every_role (.mid (.notSame ax))
  let Positions := {X : Set K // R.holds X (.mid (.pos ax))}
  have step : ∀ X : Positions, ∃ (Q : Set K) (Y : Positions),
      R.holds Q (.mid (.sep ax)) ∧ Q ⊆ X.val ∪ N ∧ Y.val ⊆ Q ∪ S := by
    intro X
    obtain ⟨Q, d, hQX, hQ, hd⟩ := R.respond_admissible (Or.inl (.generate ax)) X.property hN
    have he := (admissible_generate ax d).mp hd
    subst d
    obtain ⟨Y, d, hYQ, hY, hd⟩ := R.respond_admissible (Or.inl (.separate ax)) hQ hS
    have he := (admissible_separate ax d).mp hd
    subst d
    exact ⟨Q, ⟨Y, hY⟩, hQ, hQX, hYQ⟩
  choose Q f hQ hQX hfQ using step
  haveI : Nonempty Positions := by
    obtain ⟨X, hX⟩ := R.every_role (.mid (.pos ax))
    exact ⟨⟨X, hX⟩⟩
  obtain ⟨n, c, hc⟩ := finite_cycle f
  refine ⟨n, ⟨{
    position := fun i => (c i).val
    separator := fun i => Q (c i)
    position_role := fun i => (c i).property
    separator_role := fun i => hQ (c i)
    same_part := ?_
    next_part := ?_
  }⟩⟩
  · intro i
    exact R.part_union (hQX (c i)) (R.part_refl _ _) (R.part_empty hN (by simp [support]))
  · intro i
    rw [hc i]
    exact R.part_union (hfQ (c i)) (R.part_refl _ _) (R.part_empty hS (by simp [support]))

/-- Theorem `thm:realization-torus`, with both adjacency arguments and
finite cycle extraction proved in Lean. -/
theorem tiles_torus [Fintype K] (R : Realization D K) : TilesTorus D := by
  classical
  obtain ⟨m, ⟨H⟩⟩ := R.coordinate_cycle .h
  obtain ⟨n, ⟨V⟩⟩ := R.coordinate_cycle .v
  have cells : ∀ (i : Fin (m + 1)) (j : Fin (n + 1)),
      ∃ (t : T) (C : Set K), R.holds C (.mid (.cell t)) ∧ C ⊆ H.position i ∪ V.position j := by
    intro i j
    obtain ⟨C, d, hsub, hC, hd⟩ := R.respond_admissible (Or.inl .cell)
      (H.position_role i) (V.position_role j)
    obtain ⟨t, rfl⟩ := (admissible_cell d).mp hd
    exact ⟨t, C, hC, hsub⟩
  choose τ C hC hsub using cells
  refine ⟨m, n, ⟨{
    tile := τ
    horizontal := ?_
    vertical := ?_
  }⟩⟩
  · intro i j
    exact R.adjacency .h (τ i j) (τ (finRotate (m + 1) i) j)
      _ _ _ _ _ _ (H.position_role i) (H.separator_role i)
      (H.position_role _) (V.position_role j) (hC i j) (hC _ j)
      (hsub i j) (hsub _ j) (H.same_part i) (H.next_part i)
  · intro i j
    exact R.adjacency .v (τ i j) (τ i (finRotate (n + 1) j))
      _ _ _ _ _ _ (V.position_role j) (V.separator_role j)
      (V.position_role _) (H.position_role i) (hC i j) (hC i _)
      (by simpa only [Set.union_comm] using hsub i j)
      (by simpa only [Set.union_comm] using hsub i (finRotate (n + 1) j))
      (V.same_part j) (V.next_part j)

end Realization

theorem finiteRealizable_tilesTorus (D : Wang T) : FiniteRealizable D → TilesTorus D := by
  rintro ⟨n, ⟨R⟩⟩
  exact R.tiles_torus

end Medvedev
