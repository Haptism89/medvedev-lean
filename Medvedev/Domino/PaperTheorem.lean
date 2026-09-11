import Medvedev.Domino.MachineCode
import Medvedev.Domino.Colored
import Medvedev.Domino.TapeSemantics

namespace Medvedev.Domino

/-- The downloaded paper's common-period plane-tiling formulation, with
literal equality of edge colours, for the explicitly specified machine model.
The output is finite because its labels are finite tuples of Fin indices. -/
theorem MachineCode.halts_iff_colored_periodic (c : MachineCode) :
    c.Halts ↔ ∃ t : PlaneTiling (coloredSystem c.domino.system), t.Periodic := by
  rw [← tilesTorus_iff_periodic_plane, tilesTorus_colored_iff, c.domino_correct]

/-- The domino theorem also holds for an independently presented tape:
absolute head position and a total function on all natural-number cells. -/
theorem MachineCode.absolute_domino_correct (c : MachineCode) :
    TilesTorus c.domino.system ↔ c.machine.AbsoluteHalts :=
  c.domino_correct.trans c.machine.halts_iff_absoluteHalts

theorem MachineCode.absolute_nonhalting_iff_valid (c : MachineCode) :
    ¬ c.machine.AbsoluteHalts ↔ Formula.InML c.formula := by
  rw [← c.machine.halts_iff_absoluteHalts]
  exact c.nonhalting_iff_valid

end Medvedev.Domino
