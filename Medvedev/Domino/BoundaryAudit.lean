import Medvedev.Domino.QuantifierChecks

/-!
Audit of exact dimensions and finite-window boundary semantics. The period
obstruction is transported to the actual finite Boolean domino code. Tape
parsing is used only after proving that both words have exactly one head.
-/

namespace Medvedev.Domino

/-- A positive word with exactly one state-bearing cell. -/
def WellFormed {Q Γ : Type} (u : List (Cell Q Γ)) : Prop :=
  ∃ l r q a, u = plainWord l ++ headCell q a :: plainWord r

/-- On the stated domain, parsing loses no symbols or extra heads. -/
theorem WellFormed.reconstruct {Q Γ : Type} {u : List (Cell Q Γ)}
    (hu : WellFormed u) {c : TapeCfg Q Γ} (hc : parseWord u = some c) (blank : Γ) :
    u = c.word blank 0 := by
  obtain ⟨l, r, q, a, rfl⟩ := hu
  rw [parse_plain_head] at hc
  cases Option.some.inj hc
  simp [TapeCfg.word]

/-- Every finite-window transition checks single-head shape at both ends. -/
theorem WindowStep.wellFormed {Q Γ : Type} {M : Machine Q Γ} {u v : List (Cell Q Γ)}
    (h : WindowStep M u v) : WellFormed u ∧ WellFormed v := by
  cases h with
  | stay r _ l t => exact ⟨⟨l, t, _, _, rfl⟩, ⟨l, t, _, _, rfl⟩⟩
  | right r _ l t a =>
    exact ⟨⟨l, a :: t, _, _, rfl⟩,
      ⟨l ++ [r.val.write], t, r.val.next, a, by simp [plainWord, List.append_assoc]⟩⟩
  | left r _ l t a =>
    exact ⟨⟨l ++ [a], t, r.val.state, r.val.read, by simp [plainWord, List.append_assoc]⟩,
      ⟨l, r.val.write :: t, _, _, rfl⟩⟩
  | boundary r _ t => exact ⟨⟨[], t, _, _, rfl⟩, ⟨[], t, _, _, rfl⟩⟩

/-- No local-pattern nondeterminism survives as two different tape outputs. -/
theorem WindowStep.deterministic {Q Γ : Type} {M : Machine Q Γ}
    {u v z : List (Cell Q Γ)} (hv : WindowStep M u v) (hz : WindowStep M u z) : v = z := by
  obtain ⟨c, d, hc, hd, hcd⟩ := hv.parsed
  obtain ⟨c', e, hc', he, hce⟩ := hz.parsed
  have ce : c = c' := Option.some.inj (hc.symm.trans hc')
  subst c'
  have de : d = e := Option.some.inj (hcd.symm.trans hce)
  subst e
  exact (hv.wellFormed.2.reconstruct hd M.blank).trans
    (hz.wellFormed.2.reconstruct he M.blank).symm

/-- A genuinely stopped word has no transition in any fixed window. -/
theorem stoppedWord_no_step {Q Γ : Type} {M : Machine Q Γ} {u : List (Cell Q Γ)}
    (hs : stoppedWord M u) : ¬ ∃ v, WindowStep M u v := by
  rintro ⟨v, hv⟩
  obtain ⟨l, r, q, a, rfl, hs⟩ := hs
  obtain ⟨c, d, hc, _, hcd⟩ := hv.parsed
  rw [parse_plain_head] at hc
  cases Option.some.inj hc
  simp [Machine.step, hs] at hcd

/-- The converse is false: the one-cell window blocks the right-loop machine,
although its transition is defined and it never halts on the unbounded tape. -/
theorem finite_blockage_is_not_halting :
    (¬ ∃ v, WindowStep Examples.loopRight.machine (initialWord Examples.loopRight.machine 0) v) ∧
    ¬ stoppedWord Examples.loopRight.machine (initialWord Examples.loopRight.machine 0) ∧
    ¬ Examples.loopRight.Halts := by
  refine ⟨?_, ?_, Examples.loopRight_never_halts⟩
  · rintro ⟨v, hv⟩
    obtain ⟨c, d, hc, hd, hcd⟩ := hv.parsed
    have hc' : c = Examples.loopRight.machine.initialCfg := by
      simpa [initialWord, plainWord, parseWord, headCell, Machine.initialCfg] using
        (Option.some.inj hc).symm
    subst c
    have hd' : d = QuantifierChecks.rightCfg 1 :=
      Option.some.inj (hcd.symm.trans (QuantifierChecks.rightCfg_step 0))
    have he := hv.wellFormed.2.reconstruct hd Examples.loopRight.machine.blank
    rw [hd'] at he
    have hl := hv.length_eq
    rw [he] at hl
    simp [initialWord, plainWord, TapeCfg.word, QuantifierChecks.rightCfg] at hl
  · intro hs
    exact Examples.loopRight_never_halts (halts_of_windowHalts ⟨0, _, .refl, hs⟩)

/-- Relabel every tile while preserving both coordinates and every edge. -/
def mapTorus {A B : Type} {D : Wang A} {E : Wang B} (f : A → B)
    (hh : ∀ a b, D.horizontal a b → E.horizontal (f a) (f b))
    (hv : ∀ a b, D.vertical a b → E.vertical (f a) (f b)) {m n : ℕ}
    (t : Medvedev.TorusTiling D m n) : Medvedev.TorusTiling E m n where
  tile i j := f (t.tile i j)
  horizontal i j := hh _ _ (t.horizontal i j)
  vertical i j := hv _ _ (t.vertical i j)

set_option maxHeartbeats 1000000 in
/-- Decode actual Boolean tile names without changing either torus dimension.
This direction needs no choice of representatives from the enumeration. -/
theorem decodeMachineTorus {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) {m n : ℕ}
    (t : Medvedev.TorusTiling (machineCode M LQ LG).system m n) :
    Nonempty (Medvedev.TorusTiling (machineSystem M) m n) := by
  let f : Fin ((machineCells M LQ LG).length + 1) → _ := (.wall :: machineCells M LQ LG).get
  have he : (machineCode M LQ LG).system =
      (⟨fun a b => (machineSystem M).horizontal (f a) (f b),
        fun a b => (machineSystem M).vertical (f a) (f b)⟩ : Wang _) := by
    simp only [WangCode.system, machineCode, decide_eq_true_eq, f]
  rw [he] at t
  exact ⟨mapTorus f (fun _ _ h => h) (fun _ _ h => h) t⟩

/-- Specialization to the fixed finite machine-description format. -/
theorem MachineCode.decodeTorus (c : MachineCode) {m n : ℕ}
    (t : Medvedev.TorusTiling c.domino.system m n) :
    Nonempty (Medvedev.TorusTiling (machineSystem c.machine) m n) :=
  decodeMachineTorus c.machine (Listing.fin (c.states + 1)) (Listing.fin (c.symbols + 1)) t

/-- The row cycle extracted from a fixed torus has exactly that height.
Its one positive width is chosen once for all rows and is strictly below the
torus width, because at least one column is a wall. -/
theorem MachineCode.accepted_cycle_of_torus (c : MachineCode) {m n : ℕ}
    (t : Medvedev.TorusTiling c.domino.system m n) :
    ∃ w, w + 1 ≤ m ∧ ∃ u : Fin (n + 1) → List (MarkedCell (Fin (c.states + 1)) (Fin (c.symbols + 1))),
      (∀ j, (u j).length = w + 1) ∧
      ∀ j, Accepts (clockedTransducer c.machine) (u j) (u (finRotate (n + 1) j)) := by
  obtain ⟨decoded⟩ := c.decodeTorus t
  obtain ⟨w, hw, ⟨r⟩⟩ := rowCycle_of_torus ArithmeticBackground.no_torus decoded
  refine ⟨w, hw, fun j => List.ofFn fun i => ((r.vertex j).tile i).input,
    fun _ => List.length_ofFn, ?_⟩
  intro j
  refine ⟨_, _, (r.vertex j).initial, (r.vertex j).final, ?_⟩
  have h := (r.vertex j).runs
  have he : (fun i => ((r.vertex j).tile i).output) =
      (fun i => ((r.vertex (finRotate (n + 1) j)).tile i).input) := funext (r.edge j)
  rwa [he] at h

/-- The earlier parity obstruction concerns the final domino code as well
as abstract word cycles: every actual torus has even height. -/
theorem haltAfterRight_torus_height_even {m n : ℕ}
    (t : Medvedev.TorusTiling Examples.haltAfterRight.domino.system m n) : Even (n + 1) := by
  obtain ⟨_, _, u, _, hu⟩ := Examples.haltAfterRight.accepted_cycle_of_torus t
  exact QuantifierChecks.right_then_halt_cycle_even u hu

/-- A nonvacuous obstruction: this fixed code tiles some torus, yet for every
width and every odd positive height there is no such tiling. -/
theorem some_torus_but_no_odd_height :
    TilesTorus Examples.haltAfterRight.domino.system ∧ ∀ m k,
      ¬ Nonempty (Medvedev.TorusTiling Examples.haltAfterRight.domino.system m (2 * k)) := by
  refine ⟨Examples.haltAfterRight.domino_correct.mpr Examples.haltAfterRight_halts, ?_⟩
  rintro m k ⟨t⟩
  obtain ⟨s, hs⟩ := haltAfterRight_torus_height_even t
  omega

end Medvedev.Domino
