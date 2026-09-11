import Medvedev.Domino.Compiler
import Medvedev.Domino.ArithmeticAperiodic
import Medvedev.Domino.CycleHalting
import Medvedev.Domino.UnboundedMachine

namespace Medvedev.Domino

/-- The complete periodic-domino system: a fixed arithmetic background and
the clocked machine transducer, separated into strips by vertical walls. -/
def machineSystem {Q Γ : Type} (M : Machine Q Γ) :=
  compile ArithmeticBackground.system (clockedTransducer M)

/-- Halting on the unbounded blank tape is equivalent to tiling a finite
torus. The aperiodicity, reset, clock, and simulation premises have all been
discharged; this theorem has no external domino-theorem hypothesis. -/
theorem machineSystem_correct {Q Γ : Type} (M : Machine Q Γ) :
    TilesTorus (machineSystem M) ↔ M.Halts := by
  rw [machineSystem, compile_correct ArithmeticBackground.quarter ArithmeticBackground.no_torus,
    clocked_correct, windowHalts_iff_halts]

end Medvedev.Domino
