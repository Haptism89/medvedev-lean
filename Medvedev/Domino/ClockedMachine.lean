import Medvedev.Domino.MachineWords
import Medvedev.Domino.Clock
import Medvedev.Domino.Reset
import Medvedev.Domino.TransducerOperations

namespace Medvedev.Domino

abbrev MarkedCell (Q Γ : Type) := Cell Q Γ × Bool

def markedInitial {Q Γ : Type} (M : Machine Q Γ) (w : ℕ) : List (MarkedCell Q Γ) :=
  (headCell M.start M.blank, true) :: List.replicate w (plain M.blank, false)

@[simp] theorem markedInitial_machine {Q Γ : Type} (M : Machine Q Γ) (w : ℕ) :
    (markedInitial M w).map Prod.fst = initialWord M w := by
  simp [markedInitial, initialWord, plainWord]

@[simp] theorem markedInitial_clock {Q Γ : Type} (M : Machine Q Γ) (w : ℕ) :
    (markedInitial M w).map Prod.snd = Clock.word 0 w := by
  simp [markedInitial, Clock.word]

def haltCell {Q Γ : Type} (M : Machine Q Γ) (a : MarkedCell Q Γ) : Prop :=
  ∃ q, a.1.2 = some q ∧ M.transition q a.1.1 = none

def resetTransducer {Q Γ : Type} (M : Machine Q Γ) : Transducer Reset.State (MarkedCell Q Γ) :=
  Reset.transducer (fun a => noHead a.1) (haltCell M)
    (headCell M.start M.blank, true) (plain M.blank, false)

theorem halt_pattern_iff {Q Γ : Type} (M : Machine Q Γ) (u : List (MarkedCell Q Γ)) :
    (∃ l a r, u = l ++ a :: r ∧ All (fun a => noHead a.1) l ∧ haltCell M a ∧
      All (fun a => noHead a.1) r) ↔ stoppedWord M (u.map Prod.fst) := by
  constructor
  · rintro ⟨l, a, r, rfl, hl, ⟨q, hq, hstop⟩, hr⟩
    have hl' : All noHead (l.map Prod.fst) := by simpa [All, or_imp] using hl
    have hr' : All noHead (r.map Prod.fst) := by simpa [All, or_imp] using hr
    refine ⟨(l.map Prod.fst).map Prod.fst, (r.map Prod.fst).map Prod.fst, q, a.1.1, ?_, hstop⟩
    rw [List.map_append, List.map_cons, ← eq_plainWord_of_all _ hl', ← eq_plainWord_of_all _ hr']
    congr 2
    exact Prod.ext rfl hq
  · rintro ⟨l, r, q, a, hu, hstop⟩
    obtain ⟨l', rest, he, hl', hr'⟩ := List.map_eq_append_iff.mp hu
    obtain ⟨b, r', hb, hba, hbr⟩ := List.map_eq_cons_iff.mp hr'
    refine ⟨l', b, r', by simpa [hb] using he, ?_, ?_, ?_⟩
    · have h := all_plainWord (Q := Q) l
      rw [← hl'] at h
      simpa [All, or_imp] using h
    · refine ⟨q, ?_, ?_⟩
      · simpa [headCell] using congrArg Prod.snd hba
      · simpa [hba, headCell] using hstop
    · have h := all_plainWord (Q := Q) r
      rw [← hbr] at h
      simpa [All, or_imp] using h

theorem accepts_reset_iff {Q Γ : Type} (M : Machine Q Γ) (u v : List (MarkedCell Q Γ)) :
    Accepts (resetTransducer M) u v ↔
      stoppedWord M (u.map Prod.fst) ∧ v = markedInitial M (u.length - 1) := by
  rw [resetTransducer, Reset.accepts_iff, halt_pattern_iff]
  rfl

abbrev ClockedState {Q Γ : Type} (M : Machine Q Γ) :=
  ((MachinePattern M × RewritePhase) × (Unit × RewritePhase)) ⊕ Reset.State

/-- A row is either a genuine machine step with a strictly advancing marker,
or a reset from a halting configuration to the initial configuration. -/
def clockedTransducer {Q Γ : Type} (M : Machine Q Γ) : Transducer (ClockedState M) (MarkedCell Q Γ) :=
  unionTransducer (productTransducer (machineTransducer M) Clock.transducer) (resetTransducer M)

theorem accepts_clocked_iff {Q Γ : Type} (M : Machine Q Γ) (u v : List (MarkedCell Q Γ)) :
    Accepts (clockedTransducer M) u v ↔
      (WindowStep M (u.map Prod.fst) (v.map Prod.fst) ∧
        Accepts Clock.transducer (u.map Prod.snd) (v.map Prod.snd)) ∨
      (stoppedWord M (u.map Prod.fst) ∧ v = markedInitial M (u.length - 1)) := by
  rw [clockedTransducer, accepts_union_iff, accepts_product_iff, accepts_machine_iff, accepts_reset_iff]

end Medvedev.Domino
