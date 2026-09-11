import Medvedev.UpperBound
import Medvedev.Domino.StandardTM
import Mathlib.Computability.Halting

/-!
# Section 5 assembly, with the computability certificates as explicit hypotheses

The manuscript's Section 5 combines the internal reduction and the finite search
with three facts that this development does not prove: an admissible numerical
coding of formulas and of machine problems, computability of the compiled formula
and of the finite-frame checker under that coding, and non-computability of halting
for the source machine model. This file states the assembly as implications whose
hypotheses are exactly those facts, in Mathlib's vocabulary (`Primcodable`,
`Computable`, `ComputablePred`, `REPred`). Every proof composes theorems of this
project with Mathlib's closure properties; no hypothesis is discharged here, and
none is hidden in an instance. The `example`s at the end instantiate the abstract
statements with Mathlib's halting problem for `Nat.Partrec.Code`, showing that the
hypotheses are jointly satisfiable and the conclusions are not vacuous.
-/

namespace Medvedev

open Formula

section Abstract

variable {α β : Type} [Primcodable α] [Primcodable β]

/-- Theorem `thm:main`, hardness half. A computable many-one reduction of the
complement of a non-computable predicate makes the target non-computable. -/
theorem not_computablePred_of_reduction {halts : α → Prop} {valid : β → Prop} {f : α → β}
    (hf : Computable f) (hred : ∀ a, ¬ halts a ↔ valid (f a))
    (hhalt : ¬ ComputablePred halts) : ¬ ComputablePred valid := by
  intro hv
  apply hhalt
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.1 hv
  have h1 : ComputablePred fun a => g (f a) = true :=
    ComputablePred.computable_iff.2 ⟨fun a => g (f a), hg.comp hf, rfl⟩
  refine h1.not.of_eq fun a => ?_
  have h := hred a
  simp only [] at h
  rw [← h]
  exact not_not

/-- Corollary `cor:nore`, second half. A non-computable predicate whose complement
is recursively enumerable is not recursively enumerable. -/
theorem not_rePred_of_compl_re {valid : β → Prop} (hco : REPred fun b => ¬ valid b)
    (hnc : ¬ ComputablePred valid) : ¬ REPred valid :=
  fun h => hnc (ComputablePred.computable_iff_re_compl_re'.2 ⟨h, hco⟩)

/-- Proposition `prop:upper` in effective form. If `valid` is the universal closure of
a computable Boolean matrix, its complement is recursively enumerable: search for
the first failing stage. -/
theorem rePred_compl_of_check {valid : β → Prop} {check : β → ℕ → Bool}
    (hcheck : Computable₂ check) (hchar : ∀ b, valid b ↔ ∀ n, check b n = true) :
    REPred fun b => ¬ valid b := by
  have hnot : Computable₂ fun b n => !check b n := Primrec.not.to_comp.comp₂ hcheck
  refine (Partrec.rfind hnot.partrec₂).dom_re.of_eq fun b => ?_
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩ hv
    have := (hchar b).1 hv n
    simp [PFun.coe_val, Part.mem_some_iff, this] at hn
  · intro hv
    have : ∃ n, check b n = false := by
      by_contra h
      push_neg at h
      exact hv ((hchar b).2 fun n => by simpa using h n)
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by simp [PFun.coe_val, Part.mem_some_iff, hn], fun _ => trivial⟩

/-- Corollary `cor:nobound`. A computable bound on the search stages makes `valid`
computable, by a bounded conjunction computed with primitive recursion. -/
theorem computablePred_of_bound {valid : β → Prop} {check : β → ℕ → Bool}
    (hcheck : Computable₂ check) (hchar : ∀ b, valid b ↔ ∀ n, check b n = true)
    {B : β → ℕ} (hB : Computable B)
    (hbound : ∀ b, (∀ n ≤ B b, check b n = true) → valid b) :
    ComputablePred valid := by
  classical
  let all : β → ℕ → Bool := fun b k =>
    Nat.rec (motive := fun _ => Bool) true (fun y IH => IH && check b y) k
  have hall : ∀ b k, all b k = true ↔ ∀ n < k, check b n = true := by
    intro b k
    induction k with
    | zero => simp [all]
    | succ k ih =>
      simp only [all, Bool.and_eq_true] at ih ⊢
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩ n hn
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | rfl
        · exact h1 n h
        · exact h2
      · intro h
        exact ⟨fun n hn => h n (Nat.lt_succ_of_lt hn), h k (Nat.lt_succ_self k)⟩
  have hcomp : Computable fun b => all b (B b + 1) := by
    have h1 : Computable fun b => B b + 1 := Computable.succ.comp hB
    have h2 : Computable₂ fun (b : β) (p : ℕ × Bool) => p.2 && check b p.1 :=
      Primrec.and.to_comp.comp₂ (Computable.snd.comp Computable.snd).to₂
        (hcheck.comp₂ Computable.fst.to₂ (Computable.fst.comp Computable.snd).to₂)
    exact Computable.nat_rec h1 (Computable.const true) h2
  refine ComputablePred.computable_iff.2 ⟨fun b => all b (B b + 1), hcomp, ?_⟩
  funext b
  apply propext
  exact ⟨fun hv => (hall b (B b + 1)).2 fun n _ => (hchar b).1 hv n,
    fun h => hbound b fun n hn => (hall b (B b + 1)).1 h n (Nat.lt_succ_of_le hn)⟩

end Abstract

section Medvedev

/-- `prop:upper` for Medvedev logic: under a coding of formulas for which the
finite-frame checker is computable, nonvalidity is recursively enumerable. -/
theorem rePred_not_inML [Primcodable (Formula ℕ)] (hcheck : Computable₂ Formula.checkFrame) :
    REPred fun f : Formula ℕ => ¬ InML f :=
  rePred_compl_of_check hcheck Formula.pi01_characterization

/-- `thm:main`, hardness half, for the standard machine problems of
`Domino.TM0Problem`: if the compiled formula is computable and halting is not,
Medvedev validity is not computable. -/
theorem not_computablePred_inML [Primcodable (Formula ℕ)] [Primcodable Domino.TM0Problem]
    (hformula : Computable fun p : Domino.TM0Problem => p.formula)
    (hhalt : ¬ ComputablePred Domino.TM0Problem.Halts) :
    ¬ ComputablePred (InML : Formula ℕ → Prop) :=
  not_computablePred_of_reduction hformula Domino.TM0Problem.nonhalting_iff_valid hhalt

/-- Corollary `cor:nore`: under the same hypotheses together with computability of
the checker, Medvedev logic is not recursively enumerable. -/
theorem not_rePred_inML [Primcodable (Formula ℕ)] [Primcodable Domino.TM0Problem]
    (hcheck : Computable₂ Formula.checkFrame)
    (hformula : Computable fun p : Domino.TM0Problem => p.formula)
    (hhalt : ¬ ComputablePred Domino.TM0Problem.Halts) :
    ¬ REPred (InML : Formula ℕ → Prop) :=
  not_rePred_of_compl_re (rePred_not_inML hcheck) (not_computablePred_inML hformula hhalt)

/-- Corollary `cor:nobound`: no computable function bounds the countermodel size.
Stage `n` of the checker is the frame on `n + 1` points, so `n ≤ B f` means carrier
size at most `B f + 1`. -/
theorem no_computable_bound [Primcodable (Formula ℕ)] [Primcodable Domino.TM0Problem]
    (hcheck : Computable₂ Formula.checkFrame)
    (hformula : Computable fun p : Domino.TM0Problem => p.formula)
    (hhalt : ¬ ComputablePred Domino.TM0Problem.Halts) :
    ¬ ∃ B : Formula ℕ → ℕ, Computable B ∧
        ∀ f, (∀ n ≤ B f, Formula.checkFrame f n = true) → InML f :=
  fun ⟨_, hB, hbound⟩ =>
    not_computablePred_inML hformula hhalt
      (computablePred_of_bound hcheck Formula.pi01_characterization hB hbound)

end Medvedev

/-! The abstract statements are satisfiable and not vacuous: Mathlib's halting
problem for `Nat.Partrec.Code` instantiates them with the identity reduction. -/

example : ¬ ComputablePred fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom :=
  not_computablePred_of_reduction Computable.id (fun _ => Iff.rfl)
    (ComputablePred.halting_problem 0)

example : ¬ REPred fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom :=
  not_rePred_of_compl_re
    ((ComputablePred.halting_problem_re 0).of_eq fun _ => not_not.symm)
    (not_computablePred_of_reduction Computable.id (fun _ => Iff.rfl)
      (ComputablePred.halting_problem 0))

end Medvedev
