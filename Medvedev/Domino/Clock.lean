import Medvedev.Domino.LocalRewrite

namespace Medvedev.Domino.Clock

/-- The marker moves one cell right, without wrapping; reset restores it left.
For a chosen finite run, its window can be widened to fit the marker. Cyclic
heights must fit the computation and background; no square clock is required. -/
def pattern (_ : Unit) : LocalPattern Bool :=
  ⟨true, false, some (false, true), true⟩

def transducer : Transducer (Unit × RewritePhase) Bool :=
  rewriteTransducer (fun b => b = false) pattern

/-- Number of zeros before the first marker (or the full length if absent). -/
def rank : List Bool → ℕ
  | [] => 0
  | true :: _ => 0
  | false :: u => rank u + 1

theorem rank_prefix (l u : List Bool) (hl : All (fun b => b = false) l) :
    rank (l ++ u) = l.length + rank u := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h : a = false ∧ All (fun b => b = false) l := by simpa [All] using hl
    rcases h with ⟨rfl, h⟩
    simp [rank, ih h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every legal non-reset clock row strictly increases a bounded position. -/
theorem rank_increases {u v : List Bool} (h : Accepts transducer u v) :
    rank v = rank u + 1 := by
  obtain ⟨i, l, r, _, hl, _, rfl, rfl⟩ :=
    (accepts_rewrite_iff (fun b => b = false) pattern u v).mp h
  simp only [List.append_assoc, rank_prefix l _ hl]
  simp [pattern, LocalPattern.inputs, LocalPattern.outputs, rank]

def word (left right : ℕ) : List Bool := List.replicate left false ++ true :: List.replicate right false

theorem word_length (l r : ℕ) : (word l r).length = l + r + 1 := by
  simp [word]
  omega

theorem accepts_word (l r : ℕ) : Accepts transducer (word l (r + 1)) (word (l + 1) r) := by
  apply (accepts_rewrite_iff (fun b => b = false) pattern _ _).mpr
  refine ⟨(), List.replicate l false, List.replicate r false, Or.inl rfl, ?_, ?_, ?_, ?_⟩
  · simp [All]
  · simp [All]
  · simp [word, pattern, LocalPattern.inputs, List.replicate_succ]
  · simp [word, pattern, LocalPattern.outputs, List.replicate_succ', List.append_assoc]

end Medvedev.Domino.Clock
