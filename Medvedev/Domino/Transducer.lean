import Medvedev.Domino.Periodic
import Mathlib.Data.Fintype.Prod

/-!
Letter-to-letter finite-state transducers. The input letter is on the south
edge and the output letter on the north edge; states run west to east.
These are the conventions of Jeandel, Figures 6–9 and 12–13.
-/

namespace Medvedev.Domino

/-- A transducer may be nondeterministic. Its states and alphabet will be finite
when it is compiled into a finite Wang system. -/
structure Transducer (Q A : Type) where
  step : Q → A → A → Q → Prop
  initial : Q → Prop
  final : Q → Prop

structure Transition {Q A : Type} (R : Transducer Q A) where
  source : Q
  input : A
  output : A
  target : Q
  allowed : R.step source input output target
  deriving DecidableEq

instance {Q A : Type} [Finite Q] [Finite A] (R : Transducer Q A) :
    Finite (Transition R) := by
  classical
  letI := Fintype.ofFinite Q
  letI := Fintype.ofFinite A
  exact Finite.of_injective
    (fun t : Transition R => (t.source, t.input, t.output, t.target))
    (by intro a b h; cases a; cases b; simpa using h)

/-- One accepting transducer run across a nonempty finite row. Its ends are
open, with an initial state on the left and a final state on the right. -/
structure RowRun {Q A : Type} (R : Transducer Q A) (w : ℕ) where
  tile : Fin (w + 1) → Transition R
  initial : R.initial (tile 0).source
  horizontal : ∀ (i : ℕ) (hi : i + 1 < w + 1),
    (tile ⟨i, by omega⟩).target = (tile ⟨i + 1, hi⟩).source
  final : R.final (tile (Fin.last w)).target

/-- The output word of one row is exactly the input word of the next. -/
def RowRun.next {Q A : Type} {R : Transducer Q A} {w : ℕ}
    (a b : RowRun R w) : Prop := ∀ i, (a.tile i).output = (b.tile i).input

/-- A nonempty cyclic computation on a nonempty finite word. Neither an empty
word nor a sequence with a missing closing transition satisfies this predicate. -/
def HasWordCycle {Q A : Type} (R : Transducer Q A) : Prop :=
  ∃ w n, Nonempty (Cycle (RowRun.next (R := R) (w := w)) n)

/-- Synchronize two finite cycles. Their periods need not be equal. -/
theorem cycle_product {A B : Type} {R : A → A → Prop} {S : B → B → Prop}
    {m n : ℕ} (a : Cycle R m) (b : Cycle S n) :
    ∃ k, Nonempty (Cycle (fun p q : A × B => R p.1 q.1 ∧ S p.2 q.2) k) := by
  let f : Fin (m + 1) × Fin (n + 1) → Fin (m + 1) × Fin (n + 1) :=
    fun p => (finRotate (m + 1) p.1, finRotate (n + 1) p.2)
  obtain ⟨k, c, hc⟩ := finite_cycle f
  refine ⟨k, ⟨⟨fun i => (a.vertex (c i).1, b.vertex (c i).2), ?_⟩⟩⟩
  intro i
  change R (a.vertex (c i).1) (a.vertex (c (finRotate (k + 1) i)).1) ∧
    S (b.vertex (c i).2) (b.vertex (c (finRotate (k + 1) i)).2)
  rw [hc]
  exact ⟨a.edge (c i).1, b.edge (c i).2⟩

end Medvedev.Domino
