import Medvedev.Domino.FoldedTM
import Medvedev.Domino.SerializeMachine
import Medvedev.Domino.PaperTheorem

/-!
# Relation to the paper's Theorem `thm:import`

The paper *cites* the effective periodic domino theorem (Jeandel's construction)
and uses it as a black box. That use is formalized exactly as written in
`Medvedev.nonhalting_reduction` (`Reduction.lean`), where the domino theorem is an
explicit hypothesis named `periodic_domino`.

This file and the rest of `Domino/` are **additional** to the paper's argument.
They discharge that hypothesis for Mathlib's standard machine model
`Turing.TM0` with a finite input word, by an independent construction
(`machineSystem`, arithmetic aperiodic background, clock, reset, tape
simulation) that does not follow Jeandel. Nothing in the paper depends on
this; it only replaces a trusted citation by a checked proof for that model.
The paper's "empty input" is the case `w = []`.

Endpoint: `TM0Problem.nonhalting_iff_valid` — the machine does not halt on its
input iff the compiled formula is in ML.

Still outside the development: Mathlib `Computable` certificates for the
compiler and the finite checker, undecidability of halting for `TM0Problem`
(both are hypotheses in `Complexity.lean`), and Corollary `cor:inq`.
-/

namespace Medvedev.Domino
namespace StandardTM

variable {Q Γ : Type} [Inhabited Q] [Inhabited Γ] [DecidableEq Q] [DecidableEq Γ]

def stateListing (LQ : Listing Q) (w : List Γ) :
    Listing (InputLoader.State (Bool × Q) (FoldedTM.input w)) :=
  (Listing.fin ((FoldedTM.input w).length + 1)).sum
    ((Listing.fin ((FoldedTM.input w).length + 1)).sum (Listing.bool.prod LQ))

def symbolListing (LG : Listing Γ) : Listing (FoldedTM.Symbol Γ) :=
  Listing.bool.prod (LG.prod LG)

/-- Compile any explicitly enumerated finite Mathlib TM0 and finite input
to our numerical blank-tape format. This is one total executable compiler,
not a choice of a simulator after knowing whether the source halts. -/
def compile (M : Turing.TM0.Machine Γ Q) (LQ : Listing Q) (LG : Listing Γ)
    (w : List Γ) : MachineCode :=
  let input := FoldedTM.input w
  SerializeMachine.code (InputLoader.machine (FoldedTM.machine M) input)
    (stateListing LQ w) (symbolListing LG)

/-- The missing machine-model bridge: standard two-sided halting on `w`
is exactly blank-tape halting of the numerical compiled machine. All finite
states, alphabet symbols, inputs and run lengths are universally covered. -/
theorem halts_iff (M : Turing.TM0.Machine Γ Q) (LQ : Listing Q) (LG : Listing Γ)
    (w : List Γ) :
    (compile M LQ LG w).Halts ↔ (Turing.TM0.eval M w).Dom := by
  unfold compile
  rw [SerializeMachine.halts_iff, FoldedTM.loader_halts_iff]

theorem domino_correct (M : Turing.TM0.Machine Γ Q) (LQ : Listing Q) (LG : Listing Γ)
    (w : List Γ) :
    TilesTorus (compile M LQ LG w).domino.system ↔ (Turing.TM0.eval M w).Dom :=
  (compile M LQ LG w).domino_correct.trans (halts_iff M LQ LG w)

theorem nonhalting_iff_valid (M : Turing.TM0.Machine Γ Q) (LQ : Listing Q) (LG : Listing Γ)
    (w : List Γ) :
    ¬ (Turing.TM0.eval M w).Dom ↔ Formula.InML (compile M LQ LG w).formula := by
  rw [← halts_iff M LQ LG w]
  exact (compile M LQ LG w).nonhalting_iff_valid

theorem halts_iff_colored_periodic (M : Turing.TM0.Machine Γ Q)
    (LQ : Listing Q) (LG : Listing Γ) (w : List Γ) :
    (Turing.TM0.eval M w).Dom ↔
      ∃ t : PlaneTiling (coloredSystem (compile M LQ LG w).domino.system), t.Periodic :=
  (halts_iff M LQ LG w).symm.trans (compile M LQ LG w).halts_iff_colored_periodic

end StandardTM

/-- A separate numerical description of Mathlib's standard TM0. Instructions
are either a direction or a written symbol (TM0 writes and moves in separate
steps). Zero is the initial state and blank. Missing or ill-ranged entries
halt; surplus entries are ignored. The decoded semantics is Mathlib's TM0,
not the project's one-sided machine semantics. -/
structure TM0Code where
  states : ℕ
  symbols : ℕ
  table : List (Option (ℕ × (Turing.Dir ⊕ ℕ)))
  deriving DecidableEq

namespace TM0Code

def machine (c : TM0Code) : Turing.TM0.Machine (Fin (c.symbols + 1)) (Fin (c.states + 1)) :=
  fun q a => match c.table.getD (q.val * (c.symbols + 1) + a.val) none with
    | none => none
    | some (q', stmt) => if hq : q' < c.states + 1 then
        match stmt with
        | .inl d => some (⟨q', hq⟩, .move d)
        | .inr b => if hb : b < c.symbols + 1 then some (⟨q', hq⟩, .write ⟨b, hb⟩)
            else none
      else none

def compile (c : TM0Code) (w : List (Fin (c.symbols + 1))) : MachineCode :=
  StandardTM.compile c.machine (Listing.fin (c.states + 1)) (Listing.fin (c.symbols + 1)) w

theorem halts_iff (c : TM0Code) (w : List (Fin (c.symbols + 1))) :
    (c.compile w).Halts ↔ (Turing.TM0.eval c.machine w).Dom :=
  StandardTM.halts_iff c.machine _ _ w

theorem nonhalting_iff_valid (c : TM0Code) (w : List (Fin (c.symbols + 1))) :
    ¬ (Turing.TM0.eval c.machine w).Dom ↔ Formula.InML (c.compile w).formula :=
  StandardTM.nonhalting_iff_valid c.machine _ _ w

end TM0Code

/-- Finite source programs and their finite inputs, packaged into a single
type. There is no halting witness, time bound or tape bound in this input. -/
structure TM0Problem where
  program : TM0Code
  input : List (Fin (program.symbols + 1))

namespace TM0Problem

def Halts (p : TM0Problem) : Prop := (Turing.TM0.eval p.program.machine p.input).Dom
def compile (p : TM0Problem) : MachineCode := p.program.compile p.input
def formula (p : TM0Problem) : Formula ℕ := p.compile.formula

/-- A single executable transformation works for every encoded source
problem. The quantifier over problems comes after the compiler is fixed. -/
theorem compiler_correct : ∀ p : TM0Problem, p.compile.Halts ↔ p.Halts :=
  fun p => p.program.halts_iff p.input

theorem nonhalting_iff_valid (p : TM0Problem) : ¬ p.Halts ↔ Formula.InML p.formula :=
  p.program.nonhalting_iff_valid p.input

theorem domino_correct (p : TM0Problem) : TilesTorus p.compile.domino.system ↔ p.Halts :=
  p.compile.domino_correct.trans (compiler_correct p)

end TM0Problem
end Medvedev.Domino
