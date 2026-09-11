import Medvedev.Torus
import Mathlib.Data.Fintype.Pi

/-!
Finite cycles and periodic arrays used in the periodic-domino construction.
All periods in this file are positive. A cycle includes its last-to-first edge.
-/

namespace Medvedev.Domino

/-- A closed, nonempty walk in a relation; repeated vertices are permitted. -/
structure Cycle {A : Type} (R : A → A → Prop) (n : ℕ) where
  vertex : Fin (n + 1) → A
  edge : ∀ i, R (vertex i) (vertex (finRotate (n + 1) i))

/-- The pigeonhole argument in Jeandel's Lemma 3, stated for any finite graph.
No determinism of the relation is assumed. -/
theorem cycle_of_infinite_path {A : Type} [Finite A] {R : A → A → Prop}
    (a : ℕ → A) (ha : ∀ i, R (a i) (a (i + 1))) :
    ∃ n, Nonempty (Cycle R n) := by
  classical
  obtain ⟨k, l, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite a
  have pair : ∃ k l : ℕ, k < l ∧ a k = a l := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨k, l, h, he⟩
    · exact ⟨l, k, h, he.symm⟩
  obtain ⟨k, l, hlt, he⟩ := pair
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, l = k + (n + 1) := ⟨l - k - 1, by omega⟩
  refine ⟨n, ⟨⟨fun i => a (k + i.val), ?_⟩⟩⟩
  intro ⟨i, hi⟩
  by_cases hil : i < n
  · rw [finRotate_of_lt hil]
    simpa only [Nat.add_assoc] using ha (k + i)
  · have hin : i = n := by omega
    subst i
    rw [finRotate_last']
    change R (a (k + n)) (a (k + 0))
    simpa only [Nat.add_zero, he, Nat.add_assoc] using ha (k + n)

/-- Reduction of a natural coordinate modulo a positive period. -/
def index (n i : ℕ) : Fin (n + 1) := ⟨i % (n + 1), Nat.mod_lt _ (by omega)⟩

@[simp] theorem index_val (n i : ℕ) : (index n i).val = i % (n + 1) := rfl

@[simp] theorem index_coe {n : ℕ} (i : Fin (n + 1)) : index n i.val = i := by
  apply Fin.ext
  simp [index]

@[simp] theorem index_zero (n : ℕ) : index n 0 = 0 := rfl

theorem index_succ (n i : ℕ) : index n (i + 1) = finRotate (n + 1) (index n i) := by
  apply Fin.ext
  simp [finRotate_succ_apply, Fin.add_def, index, Nat.add_mod]

theorem index_add_period (n i : ℕ) : index n (i + (n + 1)) = index n i := by
  apply Fin.ext
  simp

theorem index_add (n i j : ℕ) : index n (i + j) = index n i + index n j := by
  apply Fin.ext
  simp [index, Fin.add_def, Nat.add_mod]

/-- A tiling of the first quadrant, with both directed adjacency conditions. -/
structure QuarterTiling {T : Type} (D : Wang T) where
  tile : ℕ → ℕ → T
  horizontal : ∀ i j, D.horizontal (tile i j) (tile (i + 1) j)
  vertical : ∀ i j, D.vertical (tile i j) (tile i (j + 1))

/-- Repeat a finite torus in both natural coordinates. -/
def TorusTiling.quarter {T : Type} {D : Wang T} {m n : ℕ}
    (c : Medvedev.TorusTiling D m n) : QuarterTiling D where
  tile i j := c.tile (index m i) (index n j)
  horizontal i j := by simpa only [index_succ] using c.horizontal (index m i) (index n j)
  vertical i j := by simpa only [index_succ] using c.vertical (index m i) (index n j)

/-- Internal horizontal matching in a finite row; there is no wrap edge here. -/
def Row {T : Type} (D : Wang T) (w : ℕ) :=
  {a : Fin w → T // ∀ (i : ℕ) (hi : i + 1 < w),
    D.horizontal (a ⟨i, by omega⟩) (a ⟨i + 1, hi⟩)}

instance {T : Type} [Finite T] (D : Wang T) (w : ℕ) : Finite (Row D w) := by
  classical
  letI := Fintype.ofFinite T
  unfold Row
  infer_instance

def Row.next {T : Type} {D : Wang T} {w : ℕ} (a b : Row D w) : Prop :=
  ∀ i, D.vertical (a.val i) (b.val i)

/-- Any finite-width strip from an infinite tiling can be made vertically
periodic. Only finitely many rows exist. The horizontal ends remain open. -/
theorem strip_cycle {T : Type} [Finite T] {D : Wang T}
    (c : QuarterTiling D) (w : ℕ) : ∃ n, Nonempty (Cycle (Row.next (D := D) (w := w)) n) := by
  let a : ℕ → Row D w := fun j => ⟨fun i => c.tile i.val j, fun i _ => c.horizontal i j⟩
  exact cycle_of_infinite_path a (fun j i => c.vertical i.val j)

end Medvedev.Domino
