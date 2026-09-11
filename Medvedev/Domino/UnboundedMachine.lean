import Medvedev.Domino.MachineWords

namespace Medvedev.Domino

/-- A one-sided unbounded tape, stored as two finite stacks around the head.
`left` lists the nearest cell first; `right` does likewise. Unstored cells to
the right are blank. Moving right allocates a blank cell when necessary. -/
structure TapeCfg (Q Γ : Type) where
  state : Q
  left : List Γ
  current : Γ
  right : List Γ

def TapeCfg.pad {Q Γ : Type} (c : TapeCfg Q Γ) (blank : Γ) (k : ℕ) : TapeCfg Q Γ :=
  {c with right := c.right ++ List.replicate k blank}

def TapeCfg.after {Q Γ : Type} (blank : Γ) (c : TapeCfg Q Γ) (action : Q × Γ × Move) : TapeCfg Q Γ :=
  match action.2.2 with
  | .stay => ⟨action.1, c.left, action.2.1, c.right⟩
  | .right => ⟨action.1, action.2.1 :: c.left, c.right.headD blank, c.right.tail⟩
  | .left => match c.left with
    | [] => ⟨action.1, [], action.2.1, c.right⟩
    | a :: l => ⟨action.1, l, a, action.2.1 :: c.right⟩

def Machine.initialCfg {Q Γ : Type} (M : Machine Q Γ) : TapeCfg Q Γ :=
  ⟨M.start, [], M.blank, []⟩

def Machine.step {Q Γ : Type} (M : Machine Q Γ) (c : TapeCfg Q Γ) : Option (TapeCfg Q Γ) :=
  (M.transition c.state c.current).map (TapeCfg.after M.blank c)

/-- Ordinary halting from the empty, unbounded tape. There is no bound on the
number of steps or on the cells that may be visited. -/
def Machine.Halts {Q Γ : Type} (M : Machine Q Γ) : Prop :=
  ∃ c, Relation.ReflTransGen (fun c d => M.step c = some d) M.initialCfg c ∧
    M.transition c.state c.current = none

/-- Adding explicit trailing blanks preserves the behavior of a tape. A right
move may consume one such blank, which is why the new padding size may differ. -/
theorem TapeCfg.after_pad {Q Γ : Type} (blank : Γ) (c : TapeCfg Q Γ)
    (action : Q × Γ × Move) (k : ℕ) :
    ∃ l, (c.pad blank k).after blank action = (c.after blank action).pad blank l := by
  rcases c with ⟨q, left, a, right⟩
  rcases action with ⟨q', b, move⟩
  cases move with
  | stay => exact ⟨k, rfl⟩
  | left => cases left <;> exact ⟨k, rfl⟩
  | right =>
    cases right with
    | cons a right => exact ⟨k, rfl⟩
    | nil =>
      cases k with
      | zero => exact ⟨0, rfl⟩
      | succ k => exact ⟨k, rfl⟩

theorem Machine.step_pad_backward {Q Γ : Type} (M : Machine Q Γ) (c : TapeCfg Q Γ)
    (k : ℕ) {d : TapeCfg Q Γ} (h : M.step (c.pad M.blank k) = some d) :
    ∃ e l, M.step c = some e ∧ d = e.pad M.blank l := by
  unfold Machine.step at h
  change (M.transition c.state c.current).map _ = some d at h
  obtain ⟨action, ha, hd⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨l, hl⟩ := c.after_pad M.blank action k
  refine ⟨c.after M.blank action, l, ?_, ?_⟩
  · simp [Machine.step, ha]
  · exact hd.symm.trans hl

/-- Parse the first head of a finite word. For the well-formed words in
`WindowStep`, the theorem below gives the exact unique configuration. -/
def parseWord {Q Γ : Type} : List (Cell Q Γ) → Option (TapeCfg Q Γ)
  | [] => none
  | (a, some q) :: r => some ⟨q, [], a, r.map Prod.fst⟩
  | (a, none) :: r => (parseWord r).map fun c => {c with left := c.left ++ [a]}

@[simp] theorem parse_plain_head {Q Γ : Type} (l r : List Γ) (q : Q) (a : Γ) :
    parseWord (plainWord l ++ headCell q a :: plainWord r) = some ⟨q, l.reverse, a, r⟩ := by
  induction l with
  | nil => simp [plainWord, headCell, parseWord, plain, List.map_map, Function.comp_def]
  | cons b l ih =>
    simp only [plainWord, List.map_cons, plain, List.cons_append, parseWord] at *
    rw [ih]
    simp [List.reverse_cons]

theorem WindowStep.parsed {Q Γ : Type} {M : Machine Q Γ} {u v : List (Cell Q Γ)}
    (h : WindowStep M u v) :
    ∃ c d, parseWord u = some c ∧ parseWord v = some d ∧ M.step c = some d := by
  cases h with
  | stay r hm l t =>
    refine ⟨⟨r.val.state, l.reverse, r.val.read, t⟩,
      ⟨r.val.next, l.reverse, r.val.write, t⟩, parse_plain_head _ _ _ _, parse_plain_head _ _ _ _, ?_⟩
    simp [Machine.step, r.property, TapeCfg.after, hm]
  | right r hm l t a =>
    have hu := parse_plain_head (Q := Q) l (a :: t) r.val.state r.val.read
    have hv := parse_plain_head (Q := Q) (l ++ [r.val.write]) t r.val.next a
    refine ⟨⟨r.val.state, l.reverse, r.val.read, a :: t⟩,
      ⟨r.val.next, r.val.write :: l.reverse, a, t⟩, ?_, ?_, ?_⟩
    · simpa [plainWord] using hu
    · simpa [plainWord, List.append_assoc] using hv
    · simp [Machine.step, r.property, TapeCfg.after, hm]
  | left r hm l t a =>
    have hu := parse_plain_head (Q := Q) (l ++ [a]) t r.val.state r.val.read
    have hv := parse_plain_head (Q := Q) l (r.val.write :: t) r.val.next a
    refine ⟨⟨r.val.state, a :: l.reverse, r.val.read, t⟩,
      ⟨r.val.next, l.reverse, a, r.val.write :: t⟩, ?_, ?_, ?_⟩
    · simpa [plainWord, List.append_assoc] using hu
    · simpa [plainWord] using hv
    · simp [Machine.step, r.property, TapeCfg.after, hm]
  | boundary r hm t =>
    refine ⟨⟨r.val.state, [], r.val.read, t⟩, ⟨r.val.next, [], r.val.write, t⟩, ?_, ?_, ?_⟩
    · exact parse_plain_head [] _ _ _
    · exact parse_plain_head [] _ _ _
    · simp [Machine.step, r.property, TapeCfg.after, hm]

theorem halts_of_windowHalts {Q Γ : Type} {M : Machine Q Γ} (h : WindowHalts M) : M.Halts := by
  obtain ⟨w, u, hreach, hstop⟩ := h
  have invariant : ∀ v, Relation.ReflTransGen (WindowStep M) (initialWord M w) v →
      ∃ c k, Relation.ReflTransGen (fun c d => M.step c = some d) M.initialCfg c ∧
        parseWord v = some (c.pad M.blank k) := by
    intro v hv
    induction hv with
    | refl =>
      refine ⟨M.initialCfg, w, .refl, ?_⟩
      exact parse_plain_head [] _ _ _
    | @tail v z hprev hstep ih =>
      obtain ⟨c, k, hc, hp⟩ := ih
      obtain ⟨d, e, hd, he, hde⟩ := hstep.parsed
      have hdc : d = c.pad M.blank k := Option.some.inj (hd.symm.trans hp)
      rw [hdc] at hde
      obtain ⟨c', l, hcc', hel⟩ := M.step_pad_backward c k hde
      exact ⟨c', l, hc.tail hcc', by rwa [hel] at he⟩
  obtain ⟨c, k, hc, hp⟩ := invariant u hreach
  obtain ⟨l, r, q, a, rfl, hstop⟩ := hstop
  rw [parse_plain_head] at hp
  have he := Option.some.inj hp
  have hq : q = c.state := congrArg TapeCfg.state he
  have ha : a = c.current := congrArg TapeCfg.current he
  exact ⟨c, hc, by simpa only [← hq, ← ha] using hstop⟩

def TapeCfg.word {Q Γ : Type} (c : TapeCfg Q Γ) (blank : Γ) (k : ℕ) : List (Cell Q Γ) :=
  plainWord c.left.reverse ++ headCell c.state c.current :: plainWord (c.right ++ List.replicate k blank)

/-- Every unbounded step fits in a finite window with any prescribed amount
of trailing padding at its target. A move into a previously unstored blank
requires one extra blank at the source. -/
theorem Machine.step_to_window {Q Γ : Type} (M : Machine Q Γ) {c d : TapeCfg Q Γ}
    (h : M.step c = some d) (k : ℕ) :
    ∃ l, WindowStep M (c.word M.blank l) (d.word M.blank k) := by
  obtain ⟨action, ha, hd⟩ := Option.map_eq_some_iff.mp h
  subst d
  rcases c with ⟨q, left, a, right⟩
  rcases action with ⟨q', b, move⟩
  let r : Rule M := ⟨⟨q, a, q', b, move⟩, ha⟩
  cases hm : move with
  | stay =>
    refine ⟨k, ?_⟩
    simpa [r, TapeCfg.word, TapeCfg.after, hm] using
      WindowStep.stay r hm left.reverse (right ++ List.replicate k M.blank)
  | left =>
    cases left with
    | nil =>
      refine ⟨k, ?_⟩
      simpa [r, TapeCfg.word, TapeCfg.after, hm, plainWord] using
        WindowStep.boundary r hm (right ++ List.replicate k M.blank)
    | cons x left =>
      refine ⟨k, ?_⟩
      simpa [r, TapeCfg.word, TapeCfg.after, hm, plainWord, List.append_assoc] using
        WindowStep.left r hm left.reverse (right ++ List.replicate k M.blank) x
  | right =>
    cases right with
    | nil =>
      refine ⟨k + 1, ?_⟩
      simpa [r, TapeCfg.word, TapeCfg.after, hm, plainWord, List.append_assoc, List.replicate_succ] using
        WindowStep.right r hm left.reverse (List.replicate k M.blank) M.blank
    | cons x right =>
      refine ⟨k, ?_⟩
      simpa [r, TapeCfg.word, TapeCfg.after, hm, plainWord, List.append_assoc] using
        WindowStep.right r hm left.reverse (right ++ List.replicate k M.blank) x

theorem windowHalts_of_halts {Q Γ : Type} {M : Machine Q Γ} (h : M.Halts) : WindowHalts M := by
  obtain ⟨c, hc, hstop⟩ := h
  have simulation : ∀ {a b : TapeCfg Q Γ},
      Relation.ReflTransGen (fun c d => M.step c = some d) a b →
      ∃ k l, Relation.ReflTransGen (WindowStep M) (a.word M.blank k) (b.word M.blank l) := by
    intro a b hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, 0, .refl⟩
    | @head a d had hdb ih =>
      obtain ⟨k, l, hkl⟩ := ih
      obtain ⟨s, hs⟩ := M.step_to_window had k
      exact ⟨s, l, hkl.head hs⟩
  obtain ⟨k, l, hkl⟩ := simulation hc
  refine ⟨k, c.word M.blank l, ?_, ?_⟩
  · simpa [Machine.initialCfg, TapeCfg.word, initialWord, plainWord] using hkl
  · exact ⟨c.left.reverse, c.right ++ List.replicate l M.blank, c.state, c.current, rfl, hstop⟩

/-- Finite-window halting is exactly halting on the unbounded blank tape. -/
theorem windowHalts_iff_halts {Q Γ : Type} (M : Machine Q Γ) : WindowHalts M ↔ M.Halts :=
  ⟨halts_of_windowHalts, windowHalts_of_halts⟩

end Medvedev.Domino
