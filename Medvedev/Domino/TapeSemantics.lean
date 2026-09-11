import Medvedev.Domino.UnboundedMachine
import Mathlib.Data.List.GetD

namespace Medvedev.Domino

/-- An independent tape presentation for auditing the stack semantics:
an absolute natural-number head position and a total tape function. -/
structure AbsoluteCfg (Q Γ : Type) where
  state : Q
  head : ℕ
  tape : ℕ → Γ

def AbsoluteCfg.after {Q Γ : Type} (c : AbsoluteCfg Q Γ) (action : Q × Γ × Move) : AbsoluteCfg Q Γ :=
  ⟨action.1, match action.2.2 with
    | .left => c.head - 1
    | .right => c.head + 1
    | .stay => c.head,
    Function.update c.tape c.head action.2.1⟩

def Machine.absoluteStep {Q Γ : Type} (M : Machine Q Γ) (c : AbsoluteCfg Q Γ) : Option (AbsoluteCfg Q Γ) :=
  (M.transition c.state (c.tape c.head)).map c.after

def TapeCfg.absolute {Q Γ : Type} (c : TapeCfg Q Γ) (blank : Γ) : AbsoluteCfg Q Γ :=
  ⟨c.state, c.left.length, fun i => (c.left.reverse ++ c.current :: c.right).getD i blank⟩

theorem getD_replace_middle {Γ : Type} (l : List Γ) (a b blank : Γ) (r : List Γ) (i : ℕ) :
    (l ++ b :: r).getD i blank =
      if i = l.length then b else (l ++ a :: r).getD i blank := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons x l ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem getD_append_blank {Γ : Type} (l : List Γ) (blank : Γ) (i : ℕ) :
    (l ++ [blank]).getD i blank = l.getD i blank := by
  induction l generalizing i with
  | nil => cases i <;> simp
  | cons x l ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

@[simp] theorem TapeCfg.absolute_current {Q Γ : Type} (c : TapeCfg Q Γ) (blank : Γ) :
    (c.absolute blank).tape (c.absolute blank).head = c.current := by
  simp [absolute]

/-- Every stack step has exactly the standard absolute-position meaning:
write one cell, move the head, and preserve every other tape cell. This checks
all positions, including arbitrary unstored positions to the right. -/
theorem TapeCfg.absolute_after {Q Γ : Type} (c : TapeCfg Q Γ) (blank : Γ)
    (action : Q × Γ × Move) :
    (c.after blank action).absolute blank = (c.absolute blank).after action := by
  rcases c with ⟨q, l, a, r⟩
  rcases action with ⟨q', b, move⟩
  have write : (fun i => (l.reverse ++ b :: r).getD i blank) =
      Function.update (fun i => (l.reverse ++ a :: r).getD i blank) l.length b := by
    funext i
    simpa [Function.update_apply] using getD_replace_middle l.reverse a b blank r i
  cases move with
  | stay =>
    simp only [TapeCfg.after, absolute, AbsoluteCfg.after]
    exact congrArg (AbsoluteCfg.mk q' l.length) write
  | left =>
    cases l with
    | nil => simpa [TapeCfg.after, absolute, AbsoluteCfg.after] using
        congrArg (AbsoluteCfg.mk q' 0) write
    | cons x l => simpa [TapeCfg.after, absolute, AbsoluteCfg.after, List.reverse_cons,
        List.append_assoc] using congrArg (AbsoluteCfg.mk q' l.length) write
  | right =>
    cases r with
    | cons x r => simpa [TapeCfg.after, absolute, AbsoluteCfg.after, List.reverse_cons,
        List.append_assoc] using congrArg (AbsoluteCfg.mk q' (l.length + 1)) write
    | nil =>
      have hblank : (fun i => (l.reverse ++ b :: [blank]).getD i blank) =
          fun i => (l.reverse ++ [b]).getD i blank := by
        funext i
        simpa [List.append_assoc] using getD_append_blank (l.reverse ++ [b]) blank i
      simpa [TapeCfg.after, absolute, AbsoluteCfg.after, List.reverse_cons, List.append_assoc] using
        congrArg (AbsoluteCfg.mk q' (l.length + 1)) (hblank.trans write)

theorem Machine.absolute_step {Q Γ : Type} (M : Machine Q Γ) (c : TapeCfg Q Γ) :
    (M.step c).map (fun d => d.absolute M.blank) = M.absoluteStep (c.absolute M.blank) := by
  simp only [Machine.step, absoluteStep, TapeCfg.absolute_current, Option.map_map]
  congr 1
  funext action
  exact c.absolute_after M.blank action

def Machine.AbsoluteHalts {Q Γ : Type} (M : Machine Q Γ) : Prop :=
  ∃ c, Relation.ReflTransGen (fun c d => M.absoluteStep c = some d)
      (⟨M.start, 0, fun _ => M.blank⟩ : AbsoluteCfg Q Γ) c ∧
    M.transition c.state (c.tape c.head) = none

@[simp] theorem Machine.absolute_initial {Q Γ : Type} (M : Machine Q Γ) :
    M.initialCfg.absolute M.blank = (⟨M.start, 0, fun _ => M.blank⟩ : AbsoluteCfg Q Γ) := by
  change AbsoluteCfg.mk M.start 0 (fun i => [M.blank].getD i M.blank) = _
  congr 1
  funext i
  cases i <;> simp

/-- The independently stated total-function tape semantics has precisely
the same halting predicate as the two-stack model used by the compiler. -/
theorem Machine.halts_iff_absoluteHalts {Q Γ : Type} (M : Machine Q Γ) : M.Halts ↔ M.AbsoluteHalts := by
  constructor
  · rintro ⟨c, hc, hs⟩
    refine ⟨c.absolute M.blank, ?_, by simpa using hs⟩
    rw [← M.absolute_initial]
    exact hc.lift (p := fun a b : AbsoluteCfg Q Γ => M.absoluteStep a = some b)
      (fun c => c.absolute M.blank) (fun a b h => by
      change M.absoluteStep (a.absolute M.blank) = some (b.absolute M.blank)
      rw [← M.absolute_step, h]; rfl)
  · rintro ⟨c, hc, hs⟩
    have lift : ∃ d, Relation.ReflTransGen (fun a b => M.step a = some b) M.initialCfg d ∧
        d.absolute M.blank = c := by
      clear hs
      induction hc with
      | refl => exact ⟨M.initialCfg, .refl, M.absolute_initial⟩
      | @tail a b hprev hab ih =>
        obtain ⟨d, hd, rfl⟩ := ih
        rw [← M.absolute_step] at hab
        obtain ⟨e, he, heb⟩ := Option.map_eq_some_iff.mp hab
        exact ⟨e, hd.tail he, heb⟩
    obtain ⟨d, hd, rfl⟩ := lift
    exact ⟨d, hd, by simpa using hs⟩

end Medvedev.Domino
