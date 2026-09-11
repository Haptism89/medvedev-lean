import Medvedev.Domino.FiniteCode

namespace Medvedev.Domino

/-- A finite input table. The state and symbol counts are `states + 1` and
`symbols + 1`. State zero is initial; symbol zero is blank. Entries are ordered
by `state * (symbols + 1) + symbol`. A missing entry, `none`, or an entry whose
output state/symbol is out of range halts. Extra entries are ignored. -/
structure MachineCode where
  states : ℕ
  symbols : ℕ
  table : List (Option (ℕ × ℕ × Move))
  deriving DecidableEq, Repr

def MachineCode.machine (c : MachineCode) : Machine (Fin (c.states + 1)) (Fin (c.symbols + 1)) where
  start := 0
  blank := 0
  transition q a := match c.table.getD (q.val * (c.symbols + 1) + a.val) none with
    | none => none
    | some (q', b, move) =>
      if hq : q' < c.states + 1 then
        if hb : b < c.symbols + 1 then some (⟨q', hq⟩, ⟨b, hb⟩, move) else none
      else none

def MachineCode.Halts (c : MachineCode) : Prop := c.machine.Halts

/-- The uniform executable map from finite machine descriptions to Wang
systems. No bound on running time or tape usage is supplied to this map. -/
def MachineCode.domino (c : MachineCode) : WangCode :=
  machineCode c.machine (Listing.fin (c.states + 1)) (Listing.fin (c.symbols + 1))

theorem MachineCode.domino_correct (c : MachineCode) :
    TilesTorus c.domino.system ↔ c.Halts :=
  machineCode_correct c.machine _ _

def MachineCode.formula (c : MachineCode) : Formula ℕ := c.domino.formula

/-- The domino hypothesis in the original assembly theorem is now discharged
for the explicitly defined deterministic unbounded-tape machine model. -/
theorem MachineCode.nonhalting_iff_valid (c : MachineCode) :
    ¬ c.Halts ↔ Formula.InML c.formula := by
  classical
  rw [← c.domino_correct, c.domino.correct, not_not]
  rfl

end Medvedev.Domino
