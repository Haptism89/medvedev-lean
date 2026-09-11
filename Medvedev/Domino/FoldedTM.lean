import Medvedev.Domino.InputLoader

namespace Medvedev.Domino.FoldedTM

open Turing

/-- Cell `i` stores source cells `i` and `-i-1`. The Boolean component
marks cell zero; this mark is part of the tape and survives every step. -/
abbrev Symbol (Γ : Type) := Bool × Γ × Γ

def address (negative : Bool) (i : ℕ) : ℤ :=
  if negative then -(i : ℤ) - 1 else i

def read {Γ : Type} (negative : Bool) (a : Symbol Γ) : Γ :=
  if negative then a.2.2 else a.2.1

def write {Γ : Type} (negative : Bool) (b : Γ) (a : Symbol Γ) : Symbol Γ :=
  if negative then (a.1, a.2.1, b) else (a.1, b, a.2.2)

theorem address_eq_iff (s t : Bool) (i j : ℕ) :
    address s i = address t j ↔ s = t ∧ i = j := by
  cases s <;> cases t <;> simp [address] <;> omega

/-- At the origin, crossing between source cells zero and minus one changes
tracks without moving the physical head. On the negative track directions
are reversed. In particular, a source left move is never silently clipped. -/
def motion (negative origin : Bool) : Dir → Bool × Move
  | .left => if negative then (true, .right)
      else if origin then (true, .stay) else (false, .left)
  | .right => if negative then
      if origin then (false, .stay) else (true, .left)
      else (false, .right)

def nextHead (m : Move) (i : ℕ) : ℕ :=
  match m with | .left => i - 1 | .right => i + 1 | .stay => i

def displacement : Dir → ℤ | .left => -1 | .right => 1

theorem motion_address (s : Bool) (i : ℕ) (d : Dir) :
    address (motion s (decide (i = 0)) d).1
      (nextHead (motion s (decide (i = 0)) d).2 i) =
        address s i + displacement d := by
  cases s <;> cases d <;> cases i <;>
    simp [motion, nextHead, address, displacement] <;> omega

variable {Q Γ : Type} [Inhabited Q] [Inhabited Γ]

def action (s : Bool) (a : Symbol Γ) (t : Q × TM0.Stmt Γ) :
    (Bool × Q) × Symbol Γ × Move :=
  match t.2 with
  | .write b => ((s, t.1), write s b a, .stay)
  | .move d => (((motion s a.1 d).1, t.1), a, (motion s a.1 d).2)

/-- An executable one-step simulation of Mathlib's two-sided TM0, once the
origin mark and input have been initialized. -/
def machine (M : TM0.Machine Γ Q) : Machine (Bool × Q) (Symbol Γ) where
  start := (false, default)
  blank := (false, default, default)
  transition q a := (M q.2 (read q.1 a)).map (action q.1 a)

/-- Agreement at every tape cell, with the TM0 tape's relative coordinates
translated by the current absolute source-head position. No bound on tape
usage or number of steps occurs in this relation. -/
def Represents (c : TM0.Cfg Γ Q) (d : AbsoluteCfg (Bool × Q) (Symbol Γ)) : Prop :=
  d.state.2 = c.q ∧
  (∀ i, (d.tape i).1 = decide (i = 0)) ∧
  ∀ s i, read s (d.tape i) = c.Tape.nth (address s i - address d.state.1 d.head)

omit [Inhabited Q] in
theorem represents_current {c : TM0.Cfg Γ Q}
    {d : AbsoluteCfg (Bool × Q) (Symbol Γ)} (h : Represents c d) :
    read d.state.1 (d.tape d.head) = c.Tape.head := by
  simpa using h.2.2 d.state.1 d.head

omit [Inhabited Γ] in
theorem read_update (s t : Bool) (i j : ℕ) (b : Γ) (v : ℕ → Symbol Γ) :
    read s (Function.update v j (write t b (v j)) i) =
      if address s i = address t j then b else read s (v i) := by
  simp only [address_eq_iff]
  by_cases h : i = j
  · subst i
    cases s <;> cases t <;> simp [read, write]
  · simp [h]

omit [Inhabited Q] in
theorem represents_write {c : TM0.Cfg Γ Q}
    {d : AbsoluteCfg (Bool × Q) (Symbol Γ)} (h : Represents c d) (q : Q) (b : Γ) :
    Represents ⟨q, c.Tape.write b⟩
      (d.after (action d.state.1 (d.tape d.head) (q, .write b))) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    change (Function.update d.tape d.head (write d.state.1 b (d.tape d.head)) i).1 = _
    by_cases hi : i = d.head
    · subst i
      cases hs : d.state.1 <;> simpa [write, hs] using h.2.1 d.head
    · simpa [Function.update_of_ne hi] using h.2.1 i
  · intro s i
    change read s (Function.update d.tape d.head (write d.state.1 b (d.tape d.head)) i) = _
    rw [read_update, h.2.2, Tape.write_nth]
    simp only [AbsoluteCfg.after, action, sub_eq_zero]

omit [Inhabited Q] in
theorem represents_move {c : TM0.Cfg Γ Q}
    {d : AbsoluteCfg (Bool × Q) (Symbol Γ)} (h : Represents c d) (q : Q) (dir : Dir) :
    Represents ⟨q, c.Tape.move dir⟩
      (d.after (action d.state.1 (d.tape d.head) (q, .move dir))) := by
  have ht : Function.update d.tape d.head (d.tape d.head) = d.tape :=
    Function.update_eq_self _ _
  have hp := motion_address d.state.1 d.head dir
  rw [← h.2.1 d.head] at hp
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    change (Function.update d.tape d.head (d.tape d.head) i).1 = _
    rw [ht]
    exact h.2.1 i
  · intro s i
    change read s (Function.update d.tape d.head (d.tape d.head) i) =
      (c.Tape.move dir).nth
        (address s i - address (motion d.state.1 (d.tape d.head).1 dir).1
          (nextHead (motion d.state.1 (d.tape d.head).1 dir).2 d.head))
    rw [ht, h.2.2, hp]
    cases dir <;> simp only [Tape.move_left_nth, Tape.move_right_nth, displacement] <;>
      congr 1 <;> omega

/-- Both moves and writes simulate in exactly one step. The halting branch
also agrees, allowing Mathlib's refinement theorem to prove both directions
of termination preservation. -/
theorem respects (M : TM0.Machine Γ Q) :
    Turing.Respects (TM0.step M) (machine M).absoluteStep Represents := by
  intro c d h
  have hc := represents_current h
  cases hm : M c.q c.Tape.head with
  | none =>
    simp [TM0.step, hm, Machine.absoluteStep, machine, h.1, hc]
  | some t =>
    rcases t with ⟨q, stmt⟩
    simp only [TM0.step, hm, Option.map_some]
    refine ⟨d.after (action d.state.1 (d.tape d.head) (q, stmt)), ?_, ?_⟩
    · cases stmt with
      | write b => exact represents_write h q b
      | move dir => exact represents_move h q dir
    · apply Relation.TransGen.single
      simp [hm, Machine.absoluteStep, machine, h.1, hc]

/-- Initialize an origin mark and the two tracks; one extra blank ensures
that even an empty source input produces a marked cell zero. -/
def input (w : List Γ) : List (Symbol Γ) :=
  List.ofFn (n := w.length + 1) fun i =>
    (decide (i.val = 0), w.getD i.val default, default)

theorem input_getD (w : List Γ) (i : ℕ) :
    (input w).getD i (false, default, default) =
      (decide (i = 0), w.getD i default, default) := by
  by_cases h : i < w.length + 1
  · rw [List.getD_eq_getElem _ _ (by simpa [input] using h)]
    simp only [input, List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simpa [input] using (show w.length + 1 ≤ i by omega))]
    rw [List.getD_eq_default w default (n := i) (by omega)]
    simp [show i ≠ 0 by omega]

theorem represents_initial (M : TM0.Machine Γ Q) (w : List Γ) :
    Represents (TM0.init w)
      ⟨(machine M).start, 0, fun i => (input w).getD i (machine M).blank⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    exact congrArg Prod.fst (input_getD w i)
  · intro s i
    change read s ((input w).getD i (false, default, default)) =
      (Tape.mk₁ w).nth (address s i - address false 0)
    rw [input_getD]
    cases s with
    | false =>
      change w.getD i default = (Tape.mk₁ w).nth (i : ℤ)
      rw [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]
      exact List.getD_default_eq_getI w
    | true =>
      have hi : -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) := by omega
      change default = (Tape.mk₁ w).nth ((-(i : ℤ) - 1) - 0)
      rw [sub_zero, hi]
      rfl

/-- A TM0 with arbitrary finite input is simulated by a machine started on
an entirely blank, one-sided tape. This theorem has no finiteness hypothesis
yet; finiteness is required only to serialize the table in the next module. -/
theorem loader_halts_iff (M : TM0.Machine Γ Q) (w : List Γ) :
    (InputLoader.machine (machine M) (input w)).Halts ↔ (TM0.eval M w).Dom := by
  rw [InputLoader.halts_iff]
  exact Turing.tr_eval_dom (respects M) (represents_initial M w)

end Medvedev.Domino.FoldedTM
