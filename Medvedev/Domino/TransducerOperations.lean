import Medvedev.Domino.WordRuns
import Mathlib.Data.Fintype.Sum

namespace Medvedev.Domino

theorem Runs.map {Q A P B : Type} {R : Transducer Q A} {S : Transducer P B}
    (f : Q → P) (g : A → B)
    (preserve : ∀ q a b r, R.step q a b r → S.step (f q) (g a) (g b) (f r))
    {q r : Q} {u v : List A} (h : Runs R q u v r) :
    Runs S (f q) (u.map g) (v.map g) (f r) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (preserve _ _ _ _ h) ih

def productTransducer {Q A P B : Type} (R : Transducer Q A) (S : Transducer P B) :
    Transducer (Q × P) (A × B) where
  step q a b r := R.step q.1 a.1 b.1 r.1 ∧ S.step q.2 a.2 b.2 r.2
  initial q := R.initial q.1 ∧ S.initial q.2
  final q := R.final q.1 ∧ S.final q.2

theorem product_runs {Q A P B : Type} {R : Transducer Q A} {S : Transducer P B}
    (u : List (A × B)) {v : List (A × B)} {q r : Q} {s t : P}
    (hR : Runs R q (u.map Prod.fst) (v.map Prod.fst) r)
    (hS : Runs S s (u.map Prod.snd) (v.map Prod.snd) t) :
    Runs (productTransducer R S) (q, s) u v (r, t) := by
  induction u generalizing v q s with
  | nil =>
    cases v <;> cases hR
    cases hS
    exact .nil _
  | cons a u ih =>
    cases v with
    | nil => cases hR
    | cons b v =>
      cases hR with
      | cons hR hRtail =>
        cases hS with
        | cons hS hStail => exact .cons ⟨hR, hS⟩ (ih hRtail hStail)

theorem accepts_product_iff {Q A P B : Type} (R : Transducer Q A) (S : Transducer P B)
    (u v : List (A × B)) :
    Accepts (productTransducer R S) u v ↔
      Accepts R (u.map Prod.fst) (v.map Prod.fst) ∧
      Accepts S (u.map Prod.snd) (v.map Prod.snd) := by
  constructor
  · rintro ⟨⟨q, s⟩, ⟨r, t⟩, hi, hf, h⟩
    exact ⟨⟨q, r, hi.1, hf.1,
      Runs.map (R := productTransducer R S) (S := R) Prod.fst Prod.fst (fun _ _ _ _ h => h.1) h⟩,
      ⟨s, t, hi.2, hf.2,
      Runs.map (R := productTransducer R S) (S := S) Prod.snd Prod.snd (fun _ _ _ _ h => h.2) h⟩⟩
  · rintro ⟨⟨q, r, hq, hr, hR⟩, ⟨s, t, hs, ht, hS⟩⟩
    exact ⟨(q, s), (r, t), ⟨hq, hs⟩, ⟨hr, ht⟩, product_runs u hR hS⟩

def unionTransducer {Q P A : Type} (R : Transducer Q A) (S : Transducer P A) :
    Transducer (Q ⊕ P) A where
  step q a b r := match q, r with
    | .inl q, .inl r => R.step q a b r
    | .inr q, .inr r => S.step q a b r
    | _, _ => False
  initial q := match q with
    | .inl q => R.initial q
    | .inr q => S.initial q
  final q := match q with
    | .inl q => R.final q
    | .inr q => S.final q

theorem union_runs_left {Q P A : Type} {R : Transducer Q A} {S : Transducer P A}
    (u : List A) {v : List A} {q : Q} {r : Q ⊕ P}
    (h : Runs (unionTransducer R S) (.inl q) u v r) :
    ∃ t, r = .inl t ∧ Runs R q u v t := by
  induction u generalizing v q r with
  | nil => cases h; exact ⟨q, rfl, .nil q⟩
  | cons a u ih =>
    cases h with
    | @cons _ mid _ _ b _ v hs ht =>
      cases mid with
      | inl mid =>
        obtain ⟨t, hr, htail⟩ := ih ht
        exact ⟨t, hr, .cons hs htail⟩
      | inr mid => exact hs.elim

theorem union_runs_right {Q P A : Type} {R : Transducer Q A} {S : Transducer P A}
    (u : List A) {v : List A} {q : P} {r : Q ⊕ P}
    (h : Runs (unionTransducer R S) (.inr q) u v r) :
    ∃ t, r = .inr t ∧ Runs S q u v t := by
  induction u generalizing v q r with
  | nil => cases h; exact ⟨q, rfl, .nil q⟩
  | cons a u ih =>
    cases h with
    | @cons _ mid _ _ b _ v hs ht =>
      cases mid with
      | inl mid => exact hs.elim
      | inr mid =>
        obtain ⟨t, hr, htail⟩ := ih ht
        exact ⟨t, hr, .cons hs htail⟩

theorem accepts_union_iff {Q P A : Type} (R : Transducer Q A) (S : Transducer P A)
    (u v : List A) : Accepts (unionTransducer R S) u v ↔ Accepts R u v ∨ Accepts S u v := by
  constructor
  · rintro ⟨q, r, hq, hr, h⟩
    cases q with
    | inl q =>
      obtain ⟨t, rfl, ht⟩ := union_runs_left u h
      exact Or.inl ⟨q, t, hq, hr, ht⟩
    | inr q =>
      obtain ⟨t, rfl, ht⟩ := union_runs_right u h
      exact Or.inr ⟨q, t, hq, hr, ht⟩
  · rintro (⟨q, r, hq, hr, h⟩ | ⟨q, r, hq, hr, h⟩)
    · refine ⟨.inl q, .inl r, hq, hr, ?_⟩
      simpa using h.map Sum.inl id (fun _ _ _ _ h => h)
    · refine ⟨.inr q, .inr r, hq, hr, ?_⟩
      simpa using h.map Sum.inr id (fun _ _ _ _ h => h)

end Medvedev.Domino
