import Medvedev.Domino.WordRuns

namespace Medvedev.Domino

/-- A rewrite changes one cell or two adjacent cells. `allowPrefix = false` anchors
the rewrite at the left boundary. The surrounding cells are copied unchanged. -/
structure LocalPattern (A : Type) where
  input : A
  output : A
  second : Option (A × A)
  allowPrefix : Bool

def LocalPattern.inputs {A : Type} (p : LocalPattern A) : List A :=
  p.input :: p.second.toList.map Prod.fst

def LocalPattern.outputs {A : Type} (p : LocalPattern A) : List A :=
  p.output :: p.second.toList.map Prod.snd

inductive RewritePhase
  | before | middle | after
  deriving DecidableEq, Fintype

inductive RewriteStep {I A : Type} (P : A → Prop) (p : I → LocalPattern A) :
    (I × RewritePhase) → A → A → (I × RewritePhase) → Prop
  | copyBefore (i : I) (a : A) : (p i).allowPrefix = true → P a →
      RewriteStep P p (i, .before) a a (i, .before)
  | one (i : I) : (p i).second = none →
      RewriteStep P p (i, .before) (p i).input (p i).output (i, .after)
  | first (i : I) : (p i).second ≠ none →
      RewriteStep P p (i, .before) (p i).input (p i).output (i, .middle)
  | second (i : I) (a b : A) : (p i).second = some (a, b) →
      RewriteStep P p (i, .middle) a b (i, .after)
  | suffix (i : I) (a : A) : P a →
      RewriteStep P p (i, .after) a a (i, .after)

def rewriteTransducer {I A : Type} (P : A → Prop) (p : I → LocalPattern A) :
    Transducer (I × RewritePhase) A where
  step := RewriteStep P p
  initial q := q.2 = .before
  final q := q.2 = .after

def All {A : Type} (P : A → Prop) (u : List A) : Prop := ∀ a ∈ u, P a

def Rewrites {I A : Type} (P : A → Prop) (p : I → LocalPattern A) (u v : List A) : Prop :=
  ∃ i l r, ((p i).allowPrefix = true ∨ l = []) ∧ All P l ∧ All P r ∧
    u = l ++ (p i).inputs ++ r ∧ v = l ++ (p i).outputs ++ r

namespace RewriteProof

variable {I A : Type} {P : A → Prop} {p : I → LocalPattern A}

theorem after_shape (i : I) (u : List A) {v : List A} {q : I × RewritePhase}
    (h : Runs (rewriteTransducer P p) (i, .after) u v q) :
    q = (i, .after) ∧ u = v ∧ All P u := by
  induction u generalizing v q with
  | nil => cases h; simp [All]
  | cons a u ih =>
    cases h with
    | cons hs ht =>
      cases hs with
      | suffix _ _ hp =>
        obtain ⟨hq, huv, hall⟩ := ih ht
        exact ⟨hq, congrArg (List.cons a) huv, by simpa [All] using And.intro hp hall⟩

theorem middle_shape (i : I) (u : List A) {v : List A} {j : I}
    (h : Runs (rewriteTransducer P p) (i, .middle) u v (j, .after)) :
    j = i ∧ ∃ a b r, (p i).second = some (a, b) ∧ u = a :: r ∧ v = b :: r ∧ All P r := by
  cases u with
  | nil => cases h
  | cons a u =>
    cases h with
    | cons hs ht =>
      cases hs with
      | second _ _ _ hp =>
        rename_i b v
        obtain ⟨hq, huv, hall⟩ := after_shape i u ht
        exact ⟨congrArg Prod.fst hq, a, b, u, hp, rfl, congrArg (List.cons b) huv.symm, hall⟩

theorem before_shape (i : I) (u : List A) {v : List A} {j : I}
    (h : Runs (rewriteTransducer P p) (i, .before) u v (j, .after)) :
    j = i ∧ ∃ l r, ((p i).allowPrefix = true ∨ l = []) ∧ All P l ∧ All P r ∧
      u = l ++ (p i).inputs ++ r ∧ v = l ++ (p i).outputs ++ r := by
  induction u generalizing v with
  | nil => cases h
  | cons a u ih =>
    cases h with
    | cons hs ht =>
      cases hs with
      | copyBefore _ _ hp ha =>
        obtain ⟨hj, l, r, _, hl, hr, hu, hv⟩ := ih ht
        refine ⟨hj, a :: l, r, Or.inl hp, ?_, hr, ?_, ?_⟩
        · simpa [All] using And.intro ha hl
        · simpa using congrArg (List.cons a) hu
        · simpa using congrArg (List.cons a) hv
      | one _ hp =>
        obtain ⟨hq, huv, hall⟩ := after_shape i u ht
        refine ⟨congrArg Prod.fst hq, [], u, Or.inr rfl, by simp [All], hall, ?_, ?_⟩
        · simp [LocalPattern.inputs, hp]
        · simp [LocalPattern.outputs, hp, huv]
      | first _ _ =>
        obtain ⟨hj, a', b', r, hp, hu, hv, hr⟩ := middle_shape i u ht
        refine ⟨hj, [], r, Or.inr rfl, by simp [All], hr, ?_, ?_⟩
        · simp [LocalPattern.inputs, hp, hu]
        · simp [LocalPattern.outputs, hp, hv]

theorem suffix_run (i : I) (r : List A) (hr : All P r) :
    Runs (rewriteTransducer P p) (i, .after) r r (i, .after) := by
  induction r with
  | nil => exact .nil _
  | cons a r ih =>
    have hh : P a ∧ All P r := by simpa [All] using hr
    exact .cons (.suffix i a hh.1) (ih hh.2)

theorem pattern_run (i : I) : Runs (rewriteTransducer P p) (i, .before)
    (p i).inputs (p i).outputs (i, .after) := by
  cases h : (p i).second with
  | none =>
    simpa [LocalPattern.inputs, LocalPattern.outputs, h] using
      Runs.cons (RewriteStep.one (P := P) i h) (Runs.nil (R := rewriteTransducer P p) (i, .after))
  | some ab =>
    rcases ab with ⟨a, b⟩
    simpa [LocalPattern.inputs, LocalPattern.outputs, h] using
      Runs.cons (RewriteStep.first (P := P) i (by simp [h]))
        (Runs.cons (RewriteStep.second (P := P) i a b h)
          (Runs.nil (R := rewriteTransducer P p) (i, .after)))

theorem prefix_run (i : I) (l : List A) (hl : All P l) (hp : (p i).allowPrefix = true ∨ l = [])
    {u v : List A} {q : I × RewritePhase}
    (h : Runs (rewriteTransducer P p) (i, .before) u v q) :
    Runs (rewriteTransducer P p) (i, .before) (l ++ u) (l ++ v) q := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    have hh : P a ∧ All P l := by simpa [All] using hl
    have hp' : (p i).allowPrefix = true := hp.resolve_right (by simp)
    exact .cons (.copyBefore i a hp' hh.1) (ih hh.2 (Or.inl hp'))

end RewriteProof

/-- The local-rule compiler recognizes exactly one permitted rewrite,
including both boundary and copying restrictions. -/
theorem accepts_rewrite_iff {I A : Type} (P : A → Prop) (p : I → LocalPattern A) (u v : List A) :
    Accepts (rewriteTransducer P p) u v ↔ Rewrites P p u v := by
  constructor
  · rintro ⟨⟨i, qi⟩, ⟨j, qj⟩, hi, hj, h⟩
    change qi = .before at hi
    change qj = .after at hj
    subst qi
    subst qj
    obtain ⟨_, l, r, hp, hl, hr, hu, hv⟩ := RewriteProof.before_shape i u h
    exact ⟨i, l, r, hp, hl, hr, hu, hv⟩
  · rintro ⟨i, l, r, hp, hl, hr, rfl, rfl⟩
    refine ⟨(i, .before), (i, .after), rfl, rfl, ?_⟩
    simpa only [List.append_assoc] using RewriteProof.prefix_run i l hl hp
      ((RewriteProof.pattern_run i).append (RewriteProof.suffix_run i r hr))

end Medvedev.Domino
