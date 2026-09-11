import Medvedev.Domino.Examples

namespace Medvedev.Domino.AdversarialChecks

open Examples

/-- The real stay-loop machine, with its actual table-checked instruction. -/
def stayRule : Rule loopStay.machine := ⟨⟨0, 0, 0, 0, .stay⟩, rfl⟩

/-- Removing the clock admits a cyclic machine computation with no halt. -/
theorem unclocked_loop_cycle : HasWordCycle (machineTransducer loopStay.machine) := by
  apply hasWordCycle_iff.mpr
  refine ⟨0, fun _ => initialWord loopStay.machine 0, by simp [initialWord], ?_⟩
  intro i
  apply (accepts_machine_iff _ _ _).mpr
  exact WindowStep.stay stayRule rfl [] []

theorem removing_clock_is_unsound :
    ¬ loopStay.Halts ∧ TilesTorus (compile ArithmeticBackground.system (machineTransducer loopStay.machine)) :=
  ⟨loopStay_never_halts, tilesTorus_of_wordCycle ArithmeticBackground.quarter unclocked_loop_cycle⟩

def trivialBackground : Wang Unit := ⟨fun _ _ => True, fun _ _ => True⟩

/-- Ordinary suffix copying has no head and no marker. Without walls its
states need not be initial or final, so it can repeat in both directions. -/
def headlessCopy : Transition (clockedTransducer loopStay.machine) :=
  leftTransition _ (productTransition
    (⟨(.stay stayRule rfl, .after), plain 0, plain 0, (.stay stayRule rfl, .after),
      .suffix _ _ rfl⟩ : Transition (machineTransducer loopStay.machine))
    (⟨((), .after), false, false, ((), .after), .suffix _ _ rfl⟩ : Transition Clock.transducer))

theorem removing_aperiodicity_is_unsound :
    ¬ loopStay.Halts ∧ TilesTorus (compile trivialBackground (clockedTransducer loopStay.machine)) := by
  refine ⟨loopStay_never_halts, 0, 0,
    ⟨⟨fun _ _ => .cell () headlessCopy, ?_, ?_⟩⟩⟩
  · intro i j
    exact ⟨trivial, rfl⟩
  · intro i j
    exact ⟨trivial, rfl⟩

/-- A deliberately faulty reset accepts any input cell as its distinguished
head. It is kept separate from the real reset predicate. -/
def uncheckedReset : Transducer Reset.State (MarkedCell (Fin 1) (Fin 1)) :=
  Reset.transducer (fun a => noHead a.1) (fun _ => True)
    (headCell 0 0, true) (plain 0, false)

theorem unchecked_reset_cycle : HasWordCycle uncheckedReset := by
  apply hasWordCycle_iff.mpr
  refine ⟨0, fun _ => [(headCell 0 0, true)], by simp, ?_⟩
  intro i
  exact ⟨.start, .after, rfl, rfl, .cons (.firstHalt _ trivial) (.nil _)⟩

theorem removing_halt_guard_is_unsound :
    ¬ loopStay.Halts ∧ TilesTorus (compile ArithmeticBackground.system uncheckedReset) :=
  ⟨loopStay_never_halts, tilesTorus_of_wordCycle ArithmeticBackground.quarter unchecked_reset_cycle⟩

/-- A deliberately faulty horizontal relation also permits adjacent walls. -/
def emptyStrips {Q A B : Type} (D : Wang B) (R : Transducer Q A) : Wang (BoardTile R B) where
  horizontal t u := match t, u with
    | .wall, .wall => True
    | _, _ => (compile D R).horizontal t u
  vertical := (compile D R).vertical

theorem allowing_empty_strips_is_unsound :
    ¬ loopStay.Halts ∧ TilesTorus (emptyStrips ArithmeticBackground.system (clockedTransducer loopStay.machine)) :=
  ⟨loopStay_never_halts, 0, 0, ⟨⟨fun _ _ => .wall, fun _ _ => trivial, fun _ _ => trivial⟩⟩⟩

/-- The zero solution would satisfy the balance equation if digits were not
shifted by one. The actual admissibility test rejects that tile. -/
theorem positive_digits_are_essential :
    let t : ArithmeticBackground.RawTile := ⟨true, 0, 0, 0, 0⟩
    ArithmeticBackground.denominator t.double * t.north.val + t.east.val =
      ArithmeticBackground.numerator t.double * t.south.val + t.west.val ∧
    ¬ ArithmeticBackground.Balanced t := by decide

/-- The generic reset theorem cannot assert unique H-occurrence without
disjointness: overlapping predicates accept two H-cells. -/
theorem reset_overlap_counterexample :
    Accepts (Reset.transducer (fun _ : Unit => True) (fun _ => True) () ()) [(), ()] [(), ()] :=
  ⟨.start, .after, rfl, rfl,
    .cons (.firstHalt _ trivial) (.cons (.plainAfter _ trivial) (.nil _))⟩

/-- A direct witness for the actual construction, independent of the general
halting-to-tiling proof: immediate halting already fits a 2×1 torus. -/
def immediateReset : Transition (clockedTransducer haltNow.machine) :=
  rightTransition _ ⟨.start, (headCell 0 0, true), (headCell 0 0, true), .after,
    .firstHalt _ ⟨0, rfl, rfl⟩⟩

theorem immediate_halt_has_2x1_witness : Nonempty (Medvedev.TorusTiling (machineSystem haltNow.machine) 1 0) := by
  let b : ArithmeticBackground.Tile := ⟨⟨true, 0, 0, 0, 1⟩, by decide⟩
  refine ⟨⟨fun i _ => if i.val = 0 then .wall else .cell b immediateReset, ?_, ?_⟩⟩
  · intro i j
    obtain hi | hi : i = 0 ∨ i = 1 := by
      have := i.isLt
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · subst i
      rfl
    · subst i
      rfl
  · intro i j
    by_cases h : i.val = 0
    · simp only [h, if_pos]
      trivial
    · simp only [h, if_false]
      exact ⟨rfl, rfl⟩

end Medvedev.Domino.AdversarialChecks
