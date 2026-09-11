import Medvedev.Domino.Transducer

/-!
Jeandel's black-column construction in the manuscript's relational Wang format.
A white tile carries a background tile and one transducer transition. A black
tile is a wall. Vertical matching preserves the wall/white distinction.
Horizontal walls force accepting transducer runs in each intervening strip.
-/

namespace Medvedev.Domino

inductive BoardTile {Q A : Type} (R : Transducer Q A) (B : Type)
  | wall
  | cell (background : B) (transition : Transition R)
  deriving DecidableEq

namespace BoardTile

variable {Q A B : Type} {R : Transducer Q A}

def isWall : BoardTile R B → Bool
  | .wall => true
  | .cell _ _ => false

theorem eq_wall_iff (t : BoardTile R B) : t = .wall ↔ t.isWall = true := by
  cases t <;> simp [isWall]

instance [Finite Q] [Finite A] [Finite B] : Finite (BoardTile R B) := by
  classical
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite (Transition R)
  let f : BoardTile R B → Unit ⊕ (B × Transition R)
    | .wall => .inl ()
    | .cell b t => .inr (b, t)
  exact Finite.of_injective f (by intro a b h; cases a <;> cases b <;> simp_all [f])

end BoardTile

/-- No wall-wall horizontal match is allowed: every strip has positive width.
The finite height is cyclic only when the output/input letters also match. -/
def compile {Q A B : Type} (D : Wang B) (R : Transducer Q A) : Wang (BoardTile R B) where
  horizontal t u := match t, u with
    | .wall, .wall => False
    | .wall, .cell _ r => R.initial r.source
    | .cell _ r, .wall => R.final r.target
    | .cell b r, .cell c s => D.horizontal b c ∧ r.target = s.source
  vertical t u := match t, u with
    | .wall, .wall => True
    | .cell b r, .cell c s => D.vertical b c ∧ r.output = s.input
    | _, _ => False

theorem wall_preserved {Q A B : Type} {D : Wang B} {R : Transducer Q A}
    {t u : BoardTile R B} (h : (compile D R).vertical t u) : t.isWall = u.isWall := by
  cases t <;> cases u <;> simp_all [compile, BoardTile.isWall]

/-- Place a wall at column zero and a synchronized pair of open rows after it. -/
def assemble {Q A B : Type} {D : Wang B} {R : Transducer Q A} {w n : ℕ}
    (c : Cycle (fun p q : Row D (w + 1) × RowRun R w =>
      Row.next p.1 q.1 ∧ RowRun.next p.2 q.2) n) :
    Medvedev.TorusTiling (compile D R) (w + 1) n where
  tile i j := Fin.cases .wall
    (fun k => .cell ((c.vertex j).1.val k) ((c.vertex j).2.tile k)) i
  horizontal i j := by
    cases i using Fin.cases with
    | zero =>
      simpa [finRotate_of_lt (Nat.zero_lt_succ w), compile] using (c.vertex j).2.initial
    | succ i =>
      by_cases hi : i.val < w
      · have hrot : finRotate (w + 2) i.succ =
            (⟨i.val + 1, by omega⟩ : Fin (w + 1)).succ := by
          apply Fin.ext
          rw [finRotate_of_lt (show i.succ.val < w + 1 by simpa using hi)]
          rfl
        rw [hrot]
        exact ⟨(c.vertex j).1.property i.val (by omega),
          (c.vertex j).2.horizontal i.val (by omega)⟩
      · have hil : i = Fin.last w := Fin.ext (by simp; omega)
        subst i
        simpa [finRotate_last, compile] using (c.vertex j).2.final
  vertical i j := by
    cases i using Fin.cases with
    | zero => trivial
    | succ i => exact ⟨(c.edge j).1 i, (c.edge j).2 i⟩

/-- A periodic transducer computation gives a torus tiling. A fixed background
quarter-plane tiling supplies all finite-width strips; pigeonhole closes them. -/
theorem tilesTorus_of_wordCycle {Q A B : Type} [Finite B]
    {D : Wang B} {R : Transducer Q A} (background : QuarterTiling D)
    (h : HasWordCycle R) : TilesTorus (compile D R) := by
  obtain ⟨w, n, ⟨c⟩⟩ := h
  obtain ⟨m, ⟨b⟩⟩ := strip_cycle background (w + 1)
  obtain ⟨k, ⟨d⟩⟩ := cycle_product b c
  exact ⟨w + 1, k, ⟨assemble d⟩⟩

/-- A periodic tiling must contain a wall. Otherwise projection to the
background would itself be a torus tiling. -/
theorem exists_wall {Q A B : Type} {D : Wang B} {R : Transducer Q A}
    (aperiodic : ¬ TilesTorus D) {m n : ℕ}
    (c : Medvedev.TorusTiling (compile D R) m n) :
    ∃ i j, c.tile i j = .wall := by
  classical
  by_contra h
  push_neg at h
  have hc : ∀ i j, ∃ b t, c.tile i j = .cell b t := by
    intro i j
    cases ht : c.tile i j with
    | wall => exact (h i j ht).elim
    | cell b t => exact ⟨b, t, rfl⟩
  choose b t ht using hc
  apply aperiodic
  refine ⟨m, n, ⟨⟨b, ?_, ?_⟩⟩⟩
  · intro i j
    have hh := c.horizontal i j
    rw [ht, ht] at hh
    exact hh.1
  · intro i j
    have hv := c.vertical i j
    rw [ht, ht] at hv
    exact hv.1

/-- A wall is an entire vertical column, including the cyclic wrap. -/
theorem wall_column {Q A B : Type} {D : Wang B} {R : Transducer Q A} {m n : ℕ}
    (c : Medvedev.TorusTiling (compile D R) m n) (i : Fin (m + 1))
    (j : Fin (n + 1)) : (c.tile i j).isWall = (c.tile i 0).isWall := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have h := wall_preserved (c.vertical i j.castSucc)
    have hr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    rw [hr] at h
    exact h.symm.trans ih

/-- Extract the accepting rows at the original height and the specified strip
width. Neither dimension is replaced by a new existential witness. -/
theorem rowCycle_of_strip {Q A B : Type} {D : Wang B} {R : Transducer Q A} {m n : ℕ}
    (c : Medvedev.TorusTiling (compile D R) m n) (x w : ℕ)
    (left : c.tile (index m x) 0 = .wall)
    (right : c.tile (index m (x + (w + 2))) 0 = .wall)
    (inside : ∀ i : Fin (w + 1), c.tile (index m (x + (i.val + 1))) 0 ≠ .wall) :
    Nonempty (Cycle (RowRun.next (R := R) (w := w)) n) := by
  classical
  have left' : ∀ j, c.tile (index m x) j = .wall := by
    intro j
    rw [BoardTile.eq_wall_iff, wall_column c, left]
    rfl
  have right' : ∀ j, c.tile (index m (x + (w + 2))) j = .wall := by
    intro j
    rw [BoardTile.eq_wall_iff, wall_column c, right]
    rfl
  have cells : ∀ (i : Fin (w + 1)) j, ∃ b t,
      c.tile (index m (x + (i.val + 1))) j = .cell b t := by
    intro i j
    cases h : c.tile (index m (x + (i.val + 1))) j with
    | cell b t => exact ⟨b, t, rfl⟩
    | wall =>
      exfalso
      apply inside i
      rw [BoardTile.eq_wall_iff, ← wall_column c _ j, h]
      rfl
  choose b t ht using cells
  let rows : Fin (n + 1) → RowRun R w := fun j => {
    tile := fun i => t i j
    initial := by
      have h := c.horizontal (index m x) j
      rw [← index_succ, left' j] at h
      have h0 := ht 0 j
      simp only [Fin.val_zero, Nat.zero_add] at h0
      rw [h0] at h
      exact h
    horizontal := by
      intro i hi
      have h := c.horizontal (index m (x + (i + 1))) j
      rw [← index_succ] at h
      rw [ht ⟨i, by omega⟩ j] at h
      have hh : x + (i + 1) + 1 = x + (i + 1 + 1) := by omega
      rw [hh, ht ⟨i + 1, hi⟩ j] at h
      exact h.2
    final := by
      have h := c.horizontal (index m (x + (w + 1))) j
      rw [← index_succ] at h
      have hh : x + (w + 1) + 1 = x + (w + 2) := by omega
      have hlast := ht (Fin.last w) j
      simp only [Fin.val_last] at hlast
      rw [hh, right' j, hlast] at h
      exact h
  }
  refine ⟨⟨rows, ?_⟩⟩
  intro j i
  have h := c.vertical (index m (x + (i.val + 1))) j
  rw [ht, ht] at h
  exact h.2

/-- The existence-only form used by the original compiler interface. -/
theorem wordCycle_of_strip {Q A B : Type} {D : Wang B} {R : Transducer Q A} {m n : ℕ}
    (c : Medvedev.TorusTiling (compile D R) m n) (x w : ℕ)
    (left : c.tile (index m x) 0 = .wall)
    (right : c.tile (index m (x + (w + 2))) 0 = .wall)
    (inside : ∀ i : Fin (w + 1), c.tile (index m (x + (i.val + 1))) 0 ≠ .wall) :
    HasWordCycle R := ⟨w, n, rowCycle_of_strip c x w left right inside⟩

/-- The first white strip has width at most m, in a torus of width m+1.
Its cycle retains the torus's height n+1, including its closing transition.
No chosen or distinguished wall is part of the input tiling. -/
theorem rowCycle_of_torus {Q A B : Type} {D : Wang B} {R : Transducer Q A} {m n : ℕ}
    (aperiodic : ¬ TilesTorus D) (c : Medvedev.TorusTiling (compile D R) m n) :
    ∃ w, w + 1 ≤ m ∧ Nonempty (Cycle (RowRun.next (R := R) (w := w)) n) := by
  classical
  obtain ⟨i, j, hij⟩ := exists_wall aperiodic c
  have left : c.tile (index m i.val) 0 = .wall := by
    rw [index_coe, BoardTile.eq_wall_iff, ← wall_column c i j, hij]
    rfl
  have found : ∃ d : ℕ, c.tile (index m (i.val + (d + 1))) 0 = .wall := by
    exact ⟨m, by simpa only [index_add_period] using left⟩
  let d := Nat.find found
  have right := Nat.find_spec found
  change c.tile (index m (i.val + (d + 1))) 0 = .wall at right
  have hd : d ≠ 0 := by
    intro hz
    have hright : c.tile (index m (i.val + 1)) 0 = .wall := by
      simpa only [hz, Nat.zero_add] using right
    have hh := c.horizontal (index m i.val) 0
    rw [← index_succ, left, hright] at hh
    exact hh
  obtain ⟨w, hw⟩ : ∃ w : ℕ, d = w + 1 := ⟨d - 1, by omega⟩
  have hdm : d ≤ m := Nat.find_min' found (by simpa only [index_add_period] using left)
  refine ⟨w, by omega, ?_⟩
  apply rowCycle_of_strip c i.val w left
  · simpa only [← show w + 1 + 1 = w + 2 by omega, ← hw] using right
  · intro k hk
    have hmin := Nat.find_min found (show k.val < Nat.find found by change k.val < d; omega)
    exact hmin hk

/-- Forgetting the retained dimensions recovers the original converse. -/
theorem wordCycle_of_tilesTorus {Q A B : Type} {D : Wang B} {R : Transducer Q A}
    (aperiodic : ¬ TilesTorus D) (h : TilesTorus (compile D R)) : HasWordCycle R := by
  obtain ⟨m, n, ⟨c⟩⟩ := h
  obtain ⟨w, _, hc⟩ := rowCycle_of_torus aperiodic c
  exact ⟨w, n, hc⟩

/-- The complete black-column compiler theorem. The background assumptions are
exactly the two properties subsequently supplied by the arithmetic construction. -/
theorem compile_correct {Q A B : Type} [Finite B] {D : Wang B} {R : Transducer Q A}
    (background : QuarterTiling D) (aperiodic : ¬ TilesTorus D) :
    TilesTorus (compile D R) ↔ HasWordCycle R :=
  ⟨wordCycle_of_tilesTorus aperiodic, tilesTorus_of_wordCycle background⟩

end Medvedev.Domino
