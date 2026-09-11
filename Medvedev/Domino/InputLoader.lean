import Medvedev.Domino.TapeSemantics
import Mathlib.Computability.PostTuringMachine

namespace Medvedev.Domino

theorem Machine.absoluteHalts_iff_eval {Q Γ : Type} (M : Machine Q Γ) :
    M.AbsoluteHalts ↔
      (Turing.eval M.absoluteStep ⟨M.start, 0, fun _ => M.blank⟩).Dom := by
  constructor
  · rintro ⟨c, hc, hs⟩
    exact (Turing.mem_eval.mpr ⟨hc, by simp [Machine.absoluteStep, hs]⟩).1
  · intro h
    obtain ⟨hc, hs⟩ := Turing.mem_eval.mp (Part.get_mem h)
    exact ⟨_, hc, by simpa [Machine.absoluteStep] using hs⟩

theorem Machine.halts_iff_eval {Q Γ : Type} (M : Machine Q Γ) :
    M.Halts ↔ (Turing.eval M.absoluteStep ⟨M.start, 0, fun _ => M.blank⟩).Dom :=
  M.halts_iff_absoluteHalts.trans M.absoluteHalts_iff_eval

namespace InputLoader

variable {Q Γ : Type}

/-- Writing counter, returning counter, or simulated control state. Both
counters are bounded by the length of the supplied input, not the run time. -/
abbrev State (Q : Type) (w : List Γ) :=
  Fin (w.length + 1) ⊕ (Fin (w.length + 1) ⊕ Q)

def run (w : List Γ) (q : Q) : State Q w := .inr (.inr q)

/-- Hard-code a finite input into a machine that starts on a blank tape.
The initializer writes left-to-right, returns to cell zero, and starts `M`.
Every initializer transition is defined, including for the empty input. -/
def machine (M : Machine Q Γ) (w : List Γ) : Machine (State Q w) Γ where
  start := .inl 0
  blank := M.blank
  transition s a := match s with
    | .inl i => if h : i.val < w.length then
        some (.inl ⟨i.val + 1, by omega⟩, w[i.val], .right)
      else some (.inr (.inl i), a, .stay)
    | .inr (.inl i) => if h : i.val = 0 then some (run w M.start, a, .stay)
      else some (.inr (.inl ⟨i.val - 1, by omega⟩), a, .left)
    | .inr (.inr q) => (M.transition q a).map fun t => (run w t.1, t.2)

def cfg (w : List Γ) (c : AbsoluteCfg Q Γ) : AbsoluteCfg (State Q w) Γ :=
  ⟨run w c.state, c.head, c.tape⟩

theorem step_run (M : Machine Q Γ) (w : List Γ) (c : AbsoluteCfg Q Γ) :
    (machine M w).absoluteStep (cfg w c) = (M.absoluteStep c).map (cfg w) := by
  simp only [Machine.absoluteStep, machine, cfg, run, Option.map_map]
  congr 1

theorem respects (M : Machine Q Γ) (w : List Γ) :
    Turing.Respects M.absoluteStep (machine M w).absoluteStep
      (fun c d => cfg w c = d) := by
  rintro c _ rfl
  cases h : M.absoluteStep c with
  | none => simp [step_run, h]
  | some d => exact ⟨cfg w d, rfl, .single (by simp [step_run, h])⟩

def writing (M : Machine Q Γ) (w : List Γ) (k : ℕ) (hk : k ≤ w.length) :
    AbsoluteCfg (State Q w) Γ :=
  ⟨.inl ⟨k, by omega⟩, k, fun i => if i < k then w.getD i M.blank else M.blank⟩

theorem writing_step (M : Machine Q Γ) (w : List Γ) (k : ℕ) (hk : k < w.length) :
    (machine M w).absoluteStep (writing M w k (by omega)) =
      some (writing M w (k + 1) (by omega)) := by
  simp only [Machine.absoluteStep, writing, machine, dif_pos hk, Option.map_some,
    AbsoluteCfg.after]
  congr 2
  funext i
  by_cases hi : i = k
  · subst i
    simp [List.getD, hk]
  · simp only [Function.update_of_ne hi]
    by_cases hik : i < k <;> simp [hik, show (i < k + 1) ↔ (i < k) by omega]

theorem reaches_writing (M : Machine Q Γ) (w : List Γ) (k : ℕ) (hk : k ≤ w.length) :
    Turing.Reaches (machine M w).absoluteStep
      ⟨(machine M w).start, 0, fun _ => M.blank⟩ (writing M w k hk) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact (ih (by omega)).tail (writing_step M w k (by omega))

theorem return_reaches (M : Machine Q Γ) (w : List Γ) (t : ℕ → Γ)
    (k : ℕ) (hk : k ≤ w.length) :
    Turing.Reaches (machine M w).absoluteStep
      ⟨.inr (.inl ⟨k, by omega⟩), k, t⟩ ⟨run w M.start, 0, t⟩ := by
  induction k with
  | zero =>
    apply Relation.ReflTransGen.single
    simp [Machine.absoluteStep, machine, AbsoluteCfg.after, Function.update_eq_self]
  | succ k ih =>
    apply (ih (by omega)).head
    simp [Machine.absoluteStep, machine, AbsoluteCfg.after, Function.update_eq_self]

/-- A particular, finite initializer run exists for every input. Determinism
then makes termination before/inside the initializer impossible. -/
theorem initializes (M : Machine Q Γ) (w : List Γ) :
    Turing.Reaches (machine M w).absoluteStep
      ⟨(machine M w).start, 0, fun _ => (machine M w).blank⟩
      (cfg w ⟨M.start, 0, fun i => w.getD i M.blank⟩) := by
  have ht : (fun i => if i < w.length then w.getD i M.blank else M.blank) =
      fun i => w.getD i M.blank := by
    funext i
    by_cases h : i < w.length
    · simp [h]
    · rw [if_neg h, List.getD_eq_default w M.blank (by omega)]
  apply (reaches_writing M w w.length le_rfl).trans
  apply (return_reaches M w (fun i => w.getD i M.blank) w.length le_rfl).head
  simp only [Machine.absoluteStep, writing, machine, lt_self_iff_false, ↓reduceDIte,
    ht, Option.map_some, AbsoluteCfg.after, Function.update_eq_self]
  rfl

/-- Blank-tape halting of the compiled loader is equivalent to halting of
the original machine on the supplied finite input, in both directions. -/
theorem halts_iff (M : Machine Q Γ) (w : List Γ) :
    (machine M w).Halts ↔
      (Turing.eval M.absoluteStep ⟨M.start, 0, fun i => w.getD i M.blank⟩).Dom := by
  rw [Machine.halts_iff_eval, Turing.reaches_eval (initializes M w)]
  exact Turing.tr_eval_dom (respects M w) rfl

end InputLoader
end Medvedev.Domino
