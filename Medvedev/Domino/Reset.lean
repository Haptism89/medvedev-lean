import Medvedev.Domino.LocalRewrite

namespace Medvedev.Domino.Reset

inductive State
  | start | before | after
  deriving DecidableEq, Fintype

/-- The five reset-tile families of Jeandel's Figure 13, generalized to any
ordinary-cell predicate P and accepting-head predicate H. -/
inductive Step {A : Type} (P H : A → Prop) (initial blank : A) : State → A → A → State → Prop
  | firstPlain (a : A) : P a → Step P H initial blank .start a initial .before
  | firstHalt (a : A) : H a → Step P H initial blank .start a initial .after
  | plainBefore (a : A) : P a → Step P H initial blank .before a blank .before
  | halt (a : A) : H a → Step P H initial blank .before a blank .after
  | plainAfter (a : A) : P a → Step P H initial blank .after a blank .after

def transducer {A : Type} (P H : A → Prop) (initial blank : A) : Transducer State A where
  step := Step P H initial blank
  initial q := q = .start
  final q := q = .after

variable {A : Type} {P H : A → Prop} {initial blank : A}

theorem after_shape (u : List A) {v : List A} {q : State}
    (h : Runs (transducer P H initial blank) .after u v q) :
    q = .after ∧ All P u ∧ v = List.replicate u.length blank := by
  induction u generalizing v q with
  | nil => cases h; simp [All]
  | cons a u ih =>
    cases h with
    | cons hs ht =>
      cases hs with
      | plainAfter _ hp =>
        obtain ⟨hq, hu, hv⟩ := ih ht
        exact ⟨hq, by simpa [All] using And.intro hp hu,
          by simpa [List.replicate_succ] using congrArg (List.cons blank) hv⟩

theorem before_shape (u : List A) {v : List A}
    (h : Runs (transducer P H initial blank) .before u v .after) :
    (∃ l a r, u = l ++ a :: r ∧ All P l ∧ H a ∧ All P r) ∧
      v = List.replicate u.length blank := by
  induction u generalizing v with
  | nil => cases h
  | cons a u ih =>
    cases h with
    | cons hs ht =>
      cases hs with
      | plainBefore _ hp =>
        obtain ⟨⟨l, b, r, hu, hl, hb, hr⟩, hv⟩ := ih ht
        refine ⟨⟨a :: l, b, r, by simpa using congrArg (List.cons a) hu, ?_, hb, hr⟩, ?_⟩
        · simpa [All] using And.intro hp hl
        · simpa [List.replicate_succ] using congrArg (List.cons blank) hv
      | halt _ hp =>
        obtain ⟨_, hu, hv⟩ := after_shape u ht
        exact ⟨⟨[], a, u, rfl, by simp [All], hp, hu⟩,
          by simpa [List.replicate_succ] using congrArg (List.cons blank) hv⟩

theorem start_shape (u : List A) {v : List A}
    (h : Runs (transducer P H initial blank) .start u v .after) :
    (∃ l a r, u = l ++ a :: r ∧ All P l ∧ H a ∧ All P r) ∧
      v = initial :: List.replicate (u.length - 1) blank := by
  cases u with
  | nil => cases h
  | cons a u =>
    cases h with
    | cons hs ht =>
      cases hs with
      | firstPlain _ hp =>
        obtain ⟨⟨l, b, r, hu, hl, hb, hr⟩, hv⟩ := before_shape u ht
        refine ⟨⟨a :: l, b, r, by simpa using congrArg (List.cons a) hu, ?_, hb, hr⟩, ?_⟩
        · simpa [All] using And.intro hp hl
        · simpa using congrArg (List.cons initial) hv
      | firstHalt _ hp =>
        obtain ⟨_, hu, hv⟩ := after_shape u ht
        exact ⟨⟨[], a, u, rfl, by simp [All], hp, hu⟩,
          by simpa using congrArg (List.cons initial) hv⟩

theorem after_run (u : List A) (hu : All P u) :
    Runs (transducer P H initial blank) .after u (List.replicate u.length blank) .after := by
  induction u with
  | nil => exact .nil _
  | cons a u ih =>
    have h : P a ∧ All P u := by simpa [All] using hu
    exact .cons (.plainAfter a h.1) (ih h.2)

theorem before_run (l : List A) (a : A) (r : List A) (hl : All P l) (ha : H a) (hr : All P r) :
    Runs (transducer P H initial blank) .before (l ++ a :: r)
      (List.replicate (l ++ a :: r).length blank) .after := by
  induction l with
  | nil => exact .cons (.halt a ha) (after_run r hr)
  | cons b l ih =>
    have h : P b ∧ All P l := by simpa [All] using hl
    exact .cons (.plainBefore b h.1) (ih h.2)

/-- Reset acceptance selects one H-cell surrounded by P-cells, and produces
a fresh initial row of the same positive width. Uniqueness of the H-cell needs
P and H to be disjoint, as they are in the machine instantiation. -/
theorem accepts_iff (u v : List A) :
    Accepts (transducer P H initial blank) u v ↔
      (∃ l a r, u = l ++ a :: r ∧ All P l ∧ H a ∧ All P r) ∧
        v = initial :: List.replicate (u.length - 1) blank := by
  constructor
  · rintro ⟨q, r, hq, hr, h⟩
    change q = .start at hq
    change r = .after at hr
    subst q
    subst r
    exact start_shape u h
  · rintro ⟨⟨l, a, r, rfl, hl, ha, hr⟩, rfl⟩
    refine ⟨.start, .after, rfl, rfl, ?_⟩
    cases l with
    | nil => simpa using Runs.cons (Step.firstHalt a ha) (after_run r hr)
    | cons b l =>
      have h : P b ∧ All P l := by simpa [All] using hl
      simpa using Runs.cons (Step.firstPlain b h.1) (before_run l a r h.2 ha hr)

end Medvedev.Domino.Reset
