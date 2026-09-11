import Medvedev.Domino.PaperTheorem
import Medvedev.Domino.Examples
import Medvedev.QuantifierChecks

/-!
Quantifier audit: Jeandel's existence lemma changes the tiling witness, finite
runs choose a common window only after the run, and the machine-to-tiles map
is fixed before any run or period is chosen. See QUANTIFIER_AUDIT.md.
-/

namespace Medvedev.Domino

/-- End-to-end countermodel contract: the fixed compiler is evaluated on c;
the countermodel size is chosen next, and its valuation is chosen afterward. -/
theorem MachineCode.halts_iff_root_countermodel (c : MachineCode) :
    c.Halts ↔ ∃ n, ∃ v : ℕ → Set (Fin (n + 1)) → Prop,
      Formula.Persistent v ∧ ¬ Formula.Forces v Set.univ c.formula :=
  c.domino_correct.symm.trans (Medvedev.QuantifierChecks.correct_with_root_countermodel c.domino)

/-- Taking complements gives a universal, rather than existential, sequence
of successful finite checks. All machine and formula parameters stay fixed. -/
theorem MachineCode.nonhalting_iff_every_finite_check (c : MachineCode) :
    ¬ c.Halts ↔ ∀ n, Formula.checkFrame c.formula n = true :=
  c.nonhalting_iff_valid.trans (Formula.pi01_characterization c.formula)

/-- One common horizontal period for every row, not a separate period per row. -/
def PlaneTiling.HorizontallyPeriodic {T : Type} {D : Wang T} (c : PlaneTiling D) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ i j, c.tile (i + p) j = c.tile i j

/-- Jeandel, Lemma 3, p. 3: the conclusion is existence of a possibly new
periodic tiling. Repetition need not start at row zero of the supplied tiling. -/
theorem periodic_tiling_of_horizontal {T : Type} [Finite T] {D : Wang T}
    (c : PlaneTiling D) (h : c.HorizontallyPeriodic) :
    ∃ d : PlaneTiling D, d.Periodic := by
  classical
  obtain ⟨p, hp, hh⟩ := h
  cases p with
  | zero => omega
  | succ p =>
    let Rows := {r : Fin (p + 1) → T //
      ∀ i, D.horizontal (r i) (r (finRotate (p + 1) i))}
    letI := Fintype.ofFinite T
    haveI : Finite Rows := by dsimp [Rows]; infer_instance
    let rows : ℕ → Rows := fun j => ⟨fun i => c.tile i.val j, by
      intro i
      by_cases hi : i.val < p
      · simpa [finRotate_of_lt hi] using c.horizontal i.val j
      · have he : i = Fin.last p := Fin.ext (by simp; omega)
        subst i
        have hedge := c.horizontal p j
        have hwrap := hh 0 j
        simpa [finRotate_last, ← hwrap] using hedge⟩
    let next : Rows → Rows → Prop := fun a b => ∀ i, D.vertical (a.val i) (b.val i)
    have hedge (j : ℕ) : next (rows j) (rows (j + 1)) := by
      intro i
      simpa [rows] using c.vertical i.val j
    obtain ⟨n, ⟨r⟩⟩ := cycle_of_infinite_path rows hedge
    have ht : TilesTorus D := ⟨p, n, ⟨⟨fun i j => (r.vertex j).val i,
      fun i j => (r.vertex j).property i, fun i j => r.edge j i⟩⟩⟩
    exact (tilesTorus_iff_periodic_plane D).mp ht

/-- The exact existential equivalence, with the tiling quantified separately
on each side. Finiteness of the alphabet is used in the forward direction. -/
theorem exists_horizontal_iff_exists_periodic {T : Type} [Finite T] (D : Wang T) :
    (∃ c : PlaneTiling D, c.HorizontallyPeriodic) ↔ ∃ d : PlaneTiling D, d.Periodic := by
  constructor
  · rintro ⟨c, hc⟩
    exact periodic_tiling_of_horizontal c hc
  · rintro ⟨d, p, hp, hh, _⟩
    exact ⟨d, p, hp, hh⟩

/-- Strengthening the backward simulation: choose any amount of target
padding, then choose source padding for the entire finite run. The target
word of each step is literally the source word of the following step. -/
theorem Machine.reachable_to_window {Q Γ : Type} (M : Machine Q Γ)
    {a b : TapeCfg Q Γ}
    (h : Relation.ReflTransGen (fun c d => M.step c = some d) a b) (k : ℕ) :
    ∃ l, Relation.ReflTransGen (WindowStep M) (a.word M.blank l) (b.word M.blank k) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨k, .refl⟩
  | @head a d had hdb ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨s, hs⟩ := M.step_to_window had l
    exact ⟨s, hl.head hs⟩

/-- A padded window is fixed for the whole reachable computation. -/
theorem window_reachable_pad {Q Γ : Type} {M : Machine Q Γ}
    {u v : List (Cell Q Γ)} (h : Relation.ReflTransGen (WindowStep M) u v)
    (extra : List Γ) :
    Relation.ReflTransGen (WindowStep M) (u ++ plainWord extra) (v ++ plainWord extra) :=
  h.lift (fun w => w ++ plainWord extra) (fun _ _ hs => hs.pad extra)

/-- A machine halts iff all sufficiently wide blank windows permit a halting
computation. The threshold depends on M and its halting run; the terminal
word and computation may depend on the width chosen after that threshold. -/
theorem Machine.halts_iff_eventually_windowHalts {Q Γ : Type} (M : Machine Q Γ) :
    M.Halts ↔ ∃ w₀, ∀ w, w₀ ≤ w → ∃ u,
      Relation.ReflTransGen (WindowStep M) (initialWord M w) u ∧ stoppedWord M u := by
  constructor
  · intro h
    obtain ⟨w₀, u, hr, hs⟩ := windowHalts_of_halts h
    refine ⟨w₀, fun w hw => ⟨u ++ plainWord (List.replicate (w - w₀) M.blank), ?_,
      stoppedWord_pad hs _⟩⟩
    have hp := window_reachable_pad hr (List.replicate (w - w₀) M.blank)
    rwa [initialWord_pad, Nat.add_sub_of_le hw] at hp
  · rintro ⟨w₀, hw⟩
    obtain ⟨u, hr, hs⟩ := hw w₀ le_rfl
    exact halts_of_windowHalts ⟨w₀, u, hr, hs⟩

/-- Existence of some compiled torus does not assert existence at every
positive size: width one is impossible, regardless of its positive height. -/
theorem compiler_has_no_width_one {Q A B : Type} {D : Wang B} {R : Transducer Q A}
    (hD : ¬ TilesTorus D) (n : ℕ) :
    ¬ Nonempty (Medvedev.TorusTiling (compile D R) 0 n) := by
  rintro ⟨c⟩
  obtain ⟨i, j, hij⟩ := exists_wall hD c
  have hh := c.horizontal i j
  have hi : finRotate 1 i = i := Subsingleton.elim _ _
  rw [hi, hij] at hh
  exact hh

namespace QuantifierChecks

/-- The immediate-halt machine has a countermodel somewhere while its
formula remains valid on the singleton frame. The two quantifiers differ. -/
theorem halting_does_not_mean_invalid_at_every_size :
    Examples.haltNow.Halts ∧ ¬ Formula.InML Examples.haltNow.formula ∧
      Formula.FrameValid (Fin 1) Examples.haltNow.formula :=
  ⟨Examples.haltNow_halts, Examples.haltNow_formula_invalid,
    Medvedev.QuantifierChecks.recognizing_formula_valid_on_singleton Examples.haltNow.domino⟩

/-- Both adjacencies unrestricted; only the chosen tiling is under discussion. -/
def freeBoolSystem : Wang Bool := ⟨fun _ _ => True, fun _ _ => True⟩

/-- Every row is constant, but exactly row zero has value true. -/
def singleMarkedRow : PlaneTiling freeBoolSystem where
  tile _ j := decide (j = 0)
  horizontal _ _ := trivial
  vertical _ _ := trivial

/-- The original horizontally periodic tiling need not itself be periodic. -/
theorem horizontal_does_not_make_same_tiling_periodic :
    singleMarkedRow.HorizontallyPeriodic ∧ ¬ singleMarkedRow.Periodic := by
  refine ⟨⟨1, by decide, fun _ _ => rfl⟩, ?_⟩
  rintro ⟨p, hp, _, hv⟩
  have h := hv 0 0
  simp [singleMarkedRow] at h
  omega

/-- Row j has period |j|+1, with no common positive horizontal period. -/
def separateRowPeriods : PlaneTiling freeBoolSystem where
  tile i j := decide (i % (j.natAbs + 1 : ℤ) = 0)
  horizontal _ _ := trivial
  vertical _ _ := trivial

/-- Moving the period existential inside the row universal weakens the
definition. This counterexample uses a finite alphabet and actual plane tiling. -/
theorem rowwise_periods_do_not_give_common_period :
    (∀ j : ℤ, ∃ p : ℕ, 0 < p ∧ ∀ i,
      separateRowPeriods.tile (i + p) j = separateRowPeriods.tile i j) ∧
      ¬ separateRowPeriods.HorizontallyPeriodic := by
  constructor
  · intro j
    refine ⟨j.natAbs + 1, Nat.zero_lt_succ _, ?_⟩
    intro i
    simp [separateRowPeriods]
  · rintro ⟨p, hp, hh⟩
    have h := hh 0 p
    have hmod : (p : ℤ) % (p + 1) = p := Int.emod_eq_of_lt (by omega) (by omega)
    simp [separateRowPeriods, hmod] at h
    omega

/-- A concrete configuration after n moves of the never-halting right loop. -/
def rightCfg (n : ℕ) : TapeCfg (Fin 1) (Fin 1) := ⟨0, List.replicate n 0, 0, []⟩

theorem rightCfg_step (n : ℕ) :
    Examples.loopRight.machine.step (rightCfg n) = some (rightCfg (n + 1)) := by
  simp [Machine.step, MachineCode.machine, Examples.loopRight, rightCfg,
    TapeCfg.after, List.replicate_succ]

theorem rightCfg_reachable (n : ℕ) :
    Relation.ReflTransGen (fun c d => Examples.loopRight.machine.step c = some d)
      Examples.loopRight.machine.initialCfg (rightCfg n) := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.tail (rightCfg_step n)

/-- Every finite prefix fits some window, but no single window can contain
all these head positions. This uses one fixed, finite-state machine. -/
theorem finite_prefix_windows_do_not_give_uniform_bound :
    (∀ n, ∃ w, Relation.ReflTransGen (WindowStep Examples.loopRight.machine)
      (initialWord Examples.loopRight.machine w)
      ((rightCfg n).word Examples.loopRight.machine.blank 0)) ∧
      ¬ (∃ w, ∀ n, ((rightCfg n).absolute Examples.loopRight.machine.blank).head < w) := by
  constructor
  · intro n
    obtain ⟨w, hw⟩ := Examples.loopRight.machine.reachable_to_window (rightCfg_reachable n) 0
    exact ⟨w, by simpa [Machine.initialCfg, TapeCfg.word, initialWord, plainWord] using hw⟩
  · rintro ⟨w, hw⟩
    have h := hw w
    simp [TapeCfg.absolute, rightCfg] at h

/-- Read the state of a well-formed word; the default is immaterial because
every accepted row below has a head, as proved by its exact step/reset shape. -/
def stateValue (u : List (Cell (Fin 2) (Fin 1))) : ℕ :=
  match parseWord u with
  | none => 0
  | some c => c.state.val

theorem right_then_halt_step_balance {u v : List (Cell (Fin 2) (Fin 1))}
    (h : WindowStep Examples.haltAfterRight.machine u v) :
    stateValue u + stateValue v = 1 := by
  obtain ⟨c, d, hu, hv, hs⟩ := h.parsed
  have ha : c.current = 0 := @Subsingleton.elim (Fin 1) _ _ _
  by_cases hq : c.state = 0
  · have hd : d.state = 1 := by
      have hh := congrArg (Option.map TapeCfg.state) hs
      simpa [Machine.step, MachineCode.machine, Examples.haltAfterRight,
        hq, ha, TapeCfg.after] using hh.symm
    simp [stateValue, hu, hv, hq, hd]
  · have hq1 : c.state = 1 := Fin.eq_one_of_ne_zero c.state hq
    simp [Machine.step, MachineCode.machine, Examples.haltAfterRight, hq1, ha] at hs

theorem right_then_halt_stopped_state {u : List (Cell (Fin 2) (Fin 1))}
    (h : stoppedWord Examples.haltAfterRight.machine u) : stateValue u = 1 := by
  obtain ⟨l, r, q, a, rfl, hs⟩ := h
  have ha : a = 0 := @Subsingleton.elim (Fin 1) _ _ _
  have hq : q = 1 := by
    apply Fin.eq_one_of_ne_zero
    intro hz
    simp [MachineCode.machine, Examples.haltAfterRight, hz, ha] at hs
  simp [stateValue, hq]

theorem right_then_halt_row_balance {u v : List (MarkedCell (Fin 2) (Fin 1))}
    (h : Accepts (clockedTransducer Examples.haltAfterRight.machine) u v) :
    stateValue (u.map Prod.fst) + stateValue (v.map Prod.fst) = 1 := by
  rcases (accepts_clocked_iff _ _ _).mp h with hn | hs
  · exact right_then_halt_step_balance hn.1
  · have hv : stateValue (v.map Prod.fst) = 0 := by
      rw [hs.2, markedInitial_machine]
      simp [stateValue, initialWord, parseWord, headCell, MachineCode.machine]
    exact (congrArg₂ Nat.add (right_then_halt_stopped_state hs.1) hv).trans (by decide)

open scoped BigOperators in
/-- This actual one-step halting machine must alternate states 0 and 1 in
every cyclic computation. Consequently every such cycle has even height. -/
theorem right_then_halt_cycle_even {n : ℕ}
    (u : Fin (n + 1) → List (MarkedCell (Fin 2) (Fin 1)))
    (h : ∀ i, Accepts (clockedTransducer Examples.haltAfterRight.machine)
      (u i) (u (finRotate (n + 1) i))) : Even (n + 1) := by
  let s : Fin (n + 1) → ℕ := fun i => stateValue ((u i).map Prod.fst)
  have he := congrArg (fun f : Fin (n + 1) → ℕ => ∑ i, f i)
    (funext fun i => right_then_halt_row_balance (h i))
  change (∑ i, (s i + s (finRotate (n + 1) i))) = ∑ _ : Fin (n + 1), 1 at he
  rw [Finset.sum_add_distrib, Equiv.sum_comp (finRotate (n + 1)) s] at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at he
  exact ⟨∑ i, s i, he.symm⟩

/-- Arbitrarily large odd heights fail, irrespective of the word width.
This refutes the former comment claiming every sufficiently large height. -/
theorem odd_heights_impossible (k : ℕ) :
    ¬ ∃ u : Fin (2 * k + 1) → List (MarkedCell (Fin 2) (Fin 1)),
      ∀ i, Accepts (clockedTransducer Examples.haltAfterRight.machine)
        (u i) (u (finRotate (2 * k + 1) i)) := by
  rintro ⟨u, hu⟩
  obtain ⟨s, hs⟩ := right_then_halt_cycle_even u hu
  omega

end QuantifierChecks
end Medvedev.Domino
