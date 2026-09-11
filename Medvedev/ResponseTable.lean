import Medvedev.Basic
import Mathlib.Tactic.CasesM

/-! # Proposition `prop:forced-table`, universally quantified in the tile type. -/

namespace Medvedev

variable {T : Type} [DecidableEq T]

set_option maxHeartbeats 2000000

theorem admissible_generate (a : Axis) (d : Mid T) :
    Admissible (.pos a) (.notNext a) d ↔ d = .sep a := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_separate (a : Axis) (d : Mid T) :
    Admissible (.sep a) (.notSame a) d ↔ d = .pos a := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_cell (d : Mid T) :
    Admissible (.pos .h) (.pos .v) d ↔ ∃ t, d = .cell t := by
  cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_source (a : Axis) (t : T) (d : Mid T) :
    Admissible (.cell t) (.provider (.source a t)) d ↔ d = .source a t := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_candidate (a : Axis) (t : T) (d : Mid T) :
    Admissible (.cell t) (.provider (.candidate a t)) d ↔ d = .candidate a t := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_step (a : Axis) (d : Mid T) :
    Admissible (.sep a) (.provider (.step a)) d ↔ d = .step a := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_expected (a : Axis) (t : T) (d : Mid T) :
    Admissible (.source a t) (.step a) d ↔ d = .notSame a ∨ d = .expected a t := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

theorem admissible_forbidden (a : Axis) (t u : T) (d : Mid T) :
    Admissible (.expected a t) (.candidate a u) d ↔
      d = .notNext a ∨ d = .notSame a.other := by
  cases a <;> cases d <;> (try cases_type* Axis Key) <;>
    simp [Admissible, support, Axis.other, or_imp, forall_and,
      and_or_left, or_and_right, exists_or, eq_comm]

/-- The omitted-key assertion used to exclude a root response. -/
theorem demand_omits_step_key {D : Wang T} {a b : Mid T} (h : demand D a b) :
    ∃ ax : Axis, Colour.key (.step ax) ∉ support a ∧ Colour.key (.step ax) ∉ support b := by
  suffices hs : ∀ a b, OrientedDemand D a b →
      ∃ ax : Axis, Colour.key (.step ax) ∉ support a ∧ Colour.key (.step ax) ∉ support b by
    rcases h with h | h
    · exact hs a b h
    · obtain ⟨ax, ha, hb⟩ := hs b a h
      exact ⟨ax, hb, ha⟩
  intro a b h
  cases h with
  | generate a => exact ⟨.h, by simp [support]⟩
  | separate a => exact ⟨.h, by simp [support]⟩
  | cell => exact ⟨.h, by simp [support]⟩
  | source a t => exact ⟨.h, by simp [support]⟩
  | candidate a t => exact ⟨.h, by simp [support]⟩
  | step a => exact ⟨a.other, by cases a <;> simp [support, Axis.other]⟩
  | expected a t => exact ⟨a.other, by cases a <;> simp [support, Axis.other]⟩
  | forbidden a t u _ => exact ⟨a.other, by cases a <;> simp [support, Axis.other]⟩

end Medvedev
