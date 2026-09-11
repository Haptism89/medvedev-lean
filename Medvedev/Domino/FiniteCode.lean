import Medvedev.Domino.EffectiveListing
import Medvedev.Domino.Reduction
import Medvedev.Reduction

namespace Medvedev.Domino

/-- Repeated names in a finite enumeration do not affect tilability. -/
theorem tilesTorus_pullback {A B : Type} (D : Wang B) (f : A → B)
    (hf : Function.Surjective f) :
    TilesTorus (⟨fun a b => D.horizontal (f a) (f b),
      fun a b => D.vertical (f a) (f b)⟩ : Wang A) ↔ TilesTorus D := by
  constructor
  · rintro ⟨m, n, ⟨c⟩⟩
    exact ⟨m, n, ⟨⟨fun i j => f (c.tile i j), c.horizontal, c.vertical⟩⟩⟩
  · classical
    rintro ⟨m, n, ⟨c⟩⟩
    choose g hg using hf
    refine ⟨m, n, ⟨⟨fun i j => g (c.tile i j), ?_, ?_⟩⟩⟩
    · intro i j
      simpa only [hg] using c.horizontal i j
    · intro i j
      simpa only [hg] using c.vertical i j

set_option synthInstance.maxSize 256 in
instance {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ) :
    DecidableRel (machineSystem M).horizontal :=
  inferInstanceAs (DecidableRel (compile ArithmeticBackground.system (clockedTransducer M)).horizontal)

instance {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ) :
    DecidableRel (machineSystem M).vertical :=
  inferInstanceAs (DecidableRel (compile ArithmeticBackground.system (clockedTransducer M)).vertical)

/-- Enumerate the white tiles; tile zero in the final code will be the wall. -/
def machineCells {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) :=
  backgroundListing.values.flatMap fun b =>
    (clockedTransitionListing M LQ LG).values.map fun t => BoardTile.cell b t

/-- A concrete, executable Boolean compatibility table. Its input and output
enumerations use lists, with no noncomputable choice of finite encodings. -/
def machineCode {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : WangCode where
  size := (machineCells M LQ LG).length
  horizontal i j := decide ((machineSystem M).horizontal
    ((.wall :: machineCells M LQ LG).get i) ((.wall :: machineCells M LQ LG).get j))
  vertical i j := decide ((machineSystem M).vertical
    ((.wall :: machineCells M LQ LG).get i) ((.wall :: machineCells M LQ LG).get j))

set_option maxHeartbeats 1000000 in
theorem machineCode_correct {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) :
    TilesTorus (machineCode M LQ LG).system ↔ M.Halts := by
  let f : Fin ((machineCells M LQ LG).length + 1) → _ :=
    (.wall :: machineCells M LQ LG).get
  have hf : Function.Surjective f := by
    intro t
    exact List.mem_iff_get.mp
      ((boardListing backgroundListing (clockedTransitionListing M LQ LG)).complete t)
  have he : (machineCode M LQ LG).system =
      (⟨fun a b => (machineSystem M).horizontal (f a) (f b),
        fun a b => (machineSystem M).vertical (f a) (f b)⟩ : Wang _) := by
    simp only [WangCode.system, machineCode, decide_eq_true_eq, f]
  rw [he, tilesTorus_pullback _ f hf, machineSystem_correct]

end Medvedev.Domino
