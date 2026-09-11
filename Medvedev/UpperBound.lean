import Medvedev.FiniteSemantics
import Medvedev.Renaming

namespace Medvedev.Formula

variable {A : Type} [DecidableEq A]

def atoms : Formula A → Finset A
  | .atom a => {a}
  | .bot => ∅
  | .conj f g | .disj f g | .imp f g => atoms f ∪ atoms g

/-- Restriction to a finite atom alphabet, carrying its inclusion proof. -/
def restrictAtoms (s : Finset A) : (f : Formula A) → atoms f ⊆ s → Formula s
  | .atom a, h => .atom ⟨a, h (by simp [atoms])⟩
  | .bot, _ => .bot
  | .conj f g, h => .conj (restrictAtoms s f (Finset.Subset.trans Finset.subset_union_left h))
      (restrictAtoms s g (Finset.Subset.trans Finset.subset_union_right h))
  | .disj f g, h => .disj (restrictAtoms s f (Finset.Subset.trans Finset.subset_union_left h))
      (restrictAtoms s g (Finset.Subset.trans Finset.subset_union_right h))
  | .imp f g, h => .imp (restrictAtoms s f (Finset.Subset.trans Finset.subset_union_left h))
      (restrictAtoms s g (Finset.Subset.trans Finset.subset_union_right h))

theorem rename_restrictAtoms (s : Finset A) (f : Formula A) (h : atoms f ⊆ s) :
    rename Subtype.val (restrictAtoms s f h) = f := by
  revert h
  induction f <;> intro h <;> simp [restrictAtoms, rename, *]

/-- The explicit finite stage of the countermodel search in Proposition
`prop:upper`. Both valuations and worlds are exhaustively enumerated. -/
def checkFrame (f : Formula ℕ) (n : ℕ) : Bool :=
  checkFiniteFrame (K := Fin (n + 1)) (restrictAtoms f.atoms f (Finset.Subset.refl _))

theorem checkFrame_iff (f : Formula ℕ) (n : ℕ) :
    checkFrame f n = true ↔ FrameValid (Fin (n + 1)) f := by
  rw [checkFrame, checkFiniteFrame_iff]
  have h := frameValid_rename_iff (K := Fin (n + 1))
    (Subtype.val : f.atoms → ℕ) Subtype.val_injective
    (restrictAtoms f.atoms f (Finset.Subset.refl _))
  rw [rename_restrictAtoms] at h
  exact h.symm

/-- A universal-natural-number characterization with an executable Boolean
matrix. `checkFrame` contains no noncomputable definitions. -/
theorem pi01_characterization (f : Formula ℕ) : InML f ↔ ∀ n, checkFrame f n = true := by
  unfold InML
  exact forall_congr' (fun n => (checkFrame_iff f n).symm)

/-- A refutation is eventually found by the finite-frame search. -/
theorem not_inML_iff_countermodel (f : Formula ℕ) :
    ¬ InML f ↔ ∃ n, checkFrame f n = false := by
  classical
  simp only [pi01_characterization, not_forall, Bool.not_eq_true]

end Medvedev.Formula
