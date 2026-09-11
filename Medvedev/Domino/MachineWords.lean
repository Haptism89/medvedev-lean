import Medvedev.Domino.LocalRewrite
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Option

namespace Medvedev.Domino

inductive Move
  | left | right | stay
  deriving DecidableEq, Fintype, Repr

/-- A deterministic one-sided Turing-machine table. An undefined transition
halts; a left move at the leftmost tape cell stays there. -/
structure Machine (Q Γ : Type) where
  start : Q
  blank : Γ
  transition : Q → Γ → Option (Q × Γ × Move)

structure Instruction (Q Γ : Type) where
  state : Q
  read : Γ
  next : Q
  write : Γ
  move : Move
  deriving DecidableEq, Fintype

abbrev Rule {Q Γ : Type} (M : Machine Q Γ) :=
  {r : Instruction Q Γ // M.transition r.state r.read = some (r.next, r.write, r.move)}

instance {Q Γ : Type} [Finite Q] [Finite Γ] (M : Machine Q Γ) : Finite (Rule M) := by
  classical
  letI := Fintype.ofFinite Q
  letI := Fintype.ofFinite Γ
  infer_instance

abbrev Cell (Q Γ : Type) := Γ × Option Q

def plain {Q Γ : Type} (a : Γ) : Cell Q Γ := (a, none)
def headCell {Q Γ : Type} (q : Q) (a : Γ) : Cell Q Γ := (a, some q)
def plainWord {Q Γ : Type} (u : List Γ) : List (Cell Q Γ) := u.map plain
def noHead {Q Γ : Type} (a : Cell Q Γ) : Prop := a.2 = none

def initialWord {Q Γ : Type} (M : Machine Q Γ) (w : ℕ) : List (Cell Q Γ) :=
  headCell M.start M.blank :: plainWord (List.replicate w M.blank)

def stoppedWord {Q Γ : Type} (M : Machine Q Γ) (u : List (Cell Q Γ)) : Prop :=
  ∃ l r q a, u = plainWord l ++ headCell q a :: plainWord r ∧ M.transition q a = none

/-- Exact Turing steps within a finite tape window. Ordinary left/right moves
need a neighboring cell; the left boundary has the stated one-sided convention.
No move through the right edge of the window is accepted. -/
inductive WindowStep {Q Γ : Type} (M : Machine Q Γ) : List (Cell Q Γ) → List (Cell Q Γ) → Prop
  | stay (r : Rule M) (h : r.val.move = .stay) (l t : List Γ) :
      WindowStep M (plainWord l ++ headCell r.val.state r.val.read :: plainWord t)
        (plainWord l ++ headCell r.val.next r.val.write :: plainWord t)
  | right (r : Rule M) (h : r.val.move = .right) (l t : List Γ) (a : Γ) :
      WindowStep M (plainWord l ++ headCell r.val.state r.val.read :: plain a :: plainWord t)
        (plainWord l ++ plain r.val.write :: headCell r.val.next a :: plainWord t)
  | left (r : Rule M) (h : r.val.move = .left) (l t : List Γ) (a : Γ) :
      WindowStep M (plainWord l ++ plain a :: headCell r.val.state r.val.read :: plainWord t)
        (plainWord l ++ headCell r.val.next a :: plain r.val.write :: plainWord t)
  | boundary (r : Rule M) (h : r.val.move = .left) (t : List Γ) :
      WindowStep M (headCell r.val.state r.val.read :: plainWord t)
        (headCell r.val.next r.val.write :: plainWord t)

theorem WindowStep.length_eq {Q Γ : Type} {M : Machine Q Γ} {u v : List (Cell Q Γ)}
    (h : WindowStep M u v) : u.length = v.length := by
  cases h <;> simp

/-- There is a halting computation in some sufficiently large finite window.
The window size is existential, not an input restriction or a time bound. -/
def WindowHalts {Q Γ : Type} (M : Machine Q Γ) : Prop :=
  ∃ w u, Relation.ReflTransGen (WindowStep M) (initialWord M w) u ∧ stoppedWord M u

inductive MachinePattern {Q Γ : Type} (M : Machine Q Γ)
  | stay (r : Rule M) (h : r.val.move = .stay)
  | right (r : Rule M) (h : r.val.move = .right) (neighbor : Γ)
  | left (r : Rule M) (h : r.val.move = .left) (neighbor : Γ)
  | boundary (r : Rule M) (h : r.val.move = .left)
  deriving DecidableEq

instance {Q Γ : Type} [Finite Q] [Finite Γ] (M : Machine Q Γ) : Finite (MachinePattern M) := by
  classical
  letI := Fintype.ofFinite (Rule M)
  letI := Fintype.ofFinite Γ
  let f : MachinePattern M → Rule M × Option Γ × Fin 4
    | .stay r _ => (r, none, 0)
    | .right r _ a => (r, some a, 1)
    | .left r _ a => (r, some a, 2)
    | .boundary r _ => (r, none, 3)
  apply Finite.of_injective f
  intro a b h
  cases a <;> cases b <;> simp_all [f]

def machinePattern {Q Γ : Type} {M : Machine Q Γ} : MachinePattern M → LocalPattern (Cell Q Γ)
  | .stay r _ => ⟨headCell r.val.state r.val.read, headCell r.val.next r.val.write, none, true⟩
  | .right r _ a => ⟨headCell r.val.state r.val.read, plain r.val.write,
      some (plain a, headCell r.val.next a), true⟩
  | .left r _ a => ⟨plain a, headCell r.val.next a,
      some (headCell r.val.state r.val.read, plain r.val.write), true⟩
  | .boundary r _ => ⟨headCell r.val.state r.val.read, headCell r.val.next r.val.write, none, false⟩

def machineTransducer {Q Γ : Type} (M : Machine Q Γ) :
    Transducer (MachinePattern M × RewritePhase) (Cell Q Γ) :=
  rewriteTransducer noHead machinePattern

theorem all_plainWord {Q Γ : Type} (u : List Γ) : All (noHead (Q := Q)) (plainWord u) := by
  simp [All, plainWord, noHead, plain]

theorem eq_plainWord_of_all {Q Γ : Type} (u : List (Cell Q Γ)) (h : All noHead u) :
    u = plainWord (u.map Prod.fst) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have ha : noHead a ∧ All noHead u := by simpa [All] using h
    rcases a with ⟨a, q⟩
    have hq : q = none := ha.1
    simp only [plainWord, List.map_cons]
    congr 1
    · exact Prod.ext rfl hq
    · exact ih ha.2

/-- The transducer in the computation layer recognizes exactly one machine
step, with a single head and unchanged cells everywhere else. -/
theorem accepts_machine_iff {Q Γ : Type} (M : Machine Q Γ) (u v : List (Cell Q Γ)) :
    Accepts (machineTransducer M) u v ↔ WindowStep M u v := by
  rw [machineTransducer, accepts_rewrite_iff]
  constructor
  · rintro ⟨i, l, t, hp, hl, ht, rfl, rfl⟩
    have hel := eq_plainWord_of_all l hl
    have het := eq_plainWord_of_all t ht
    cases i with
    | stay r h =>
      simpa [machinePattern, LocalPattern.inputs, LocalPattern.outputs, ← hel, ← het] using
        WindowStep.stay r h (l.map Prod.fst) (t.map Prod.fst)
    | right r h a =>
      simpa [machinePattern, LocalPattern.inputs, LocalPattern.outputs, ← hel, ← het] using
        WindowStep.right r h (l.map Prod.fst) (t.map Prod.fst) a
    | left r h a =>
      simpa [machinePattern, LocalPattern.inputs, LocalPattern.outputs, ← hel, ← het] using
        WindowStep.left r h (l.map Prod.fst) (t.map Prod.fst) a
    | boundary r h =>
      have he : l = [] := by simpa [machinePattern] using hp
      subst l
      simpa [machinePattern, LocalPattern.inputs, LocalPattern.outputs, ← het] using
        WindowStep.boundary r h (t.map Prod.fst)
  · intro h
    cases h with
    | stay r h l t =>
      exact ⟨.stay r h, plainWord l, plainWord t, Or.inl rfl, all_plainWord l,
        all_plainWord t, by simp [machinePattern, LocalPattern.inputs], by simp [machinePattern, LocalPattern.outputs]⟩
    | right r h l t a =>
      exact ⟨.right r h a, plainWord l, plainWord t, Or.inl rfl, all_plainWord l,
        all_plainWord t, by simp [machinePattern, LocalPattern.inputs], by simp [machinePattern, LocalPattern.outputs]⟩
    | left r h l t a =>
      exact ⟨.left r h a, plainWord l, plainWord t, Or.inl rfl, all_plainWord l,
        all_plainWord t, by simp [machinePattern, LocalPattern.inputs], by simp [machinePattern, LocalPattern.outputs]⟩
    | boundary r h t =>
      exact ⟨.boundary r h, [], plainWord t, Or.inr rfl, by simp [All],
        all_plainWord t, by simp [machinePattern, LocalPattern.inputs], by simp [machinePattern, LocalPattern.outputs]⟩

end Medvedev.Domino
