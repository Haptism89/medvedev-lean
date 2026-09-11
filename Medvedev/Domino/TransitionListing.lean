import Medvedev.Domino.Listing
import Medvedev.Domino.TransducerOperations
import Medvedev.Domino.Reset

namespace Medvedev.Domino

def rewritePrefix {I A : Type} (P : A → Prop) (p : I → LocalPattern A)
    (LP : Listing {a // P a}) (i : I) : List (Transition (rewriteTransducer P p)) :=
  if h : (p i).allowPrefix = true then
    LP.values.map fun (a : {a // P a}) => ⟨(i, .before), a.val, a.val, (i, .before),
      RewriteStep.copyBefore (P := P) (p := p) i a.val h a.property⟩
  else []

def rewriteCore {I A : Type} (P : A → Prop) (p : I → LocalPattern A) (i : I) :
    List (Transition (rewriteTransducer P p)) :=
  match h : (p i).second with
  | none => [⟨(i, .before), (p i).input, (p i).output, (i, .after), .one i h⟩]
  | some (a, b) =>
    [⟨(i, .before), (p i).input, (p i).output, (i, .middle), .first i (by simp [h])⟩,
     ⟨(i, .middle), a, b, (i, .after), .second i a b h⟩]

def rewriteSuffix {I A : Type} (P : A → Prop) (p : I → LocalPattern A)
    (LP : Listing {a // P a}) (i : I) : List (Transition (rewriteTransducer P p)) :=
  LP.values.map fun (a : {a // P a}) => ⟨(i, .after), a.val, a.val, (i, .after),
    RewriteStep.suffix (P := P) (p := p) i a.val a.property⟩

/-- Enumerate actual rewrite transitions directly from their five constructors,
without searching a Cartesian power of all states and letters. -/
def rewriteListing {I A : Type} (P : A → Prop) (p : I → LocalPattern A)
    (LI : Listing I) (LP : Listing {a // P a}) : Listing (Transition (rewriteTransducer P p)) where
  values := LI.values.flatMap fun i => rewritePrefix P p LP i ++ rewriteCore P p i ++ rewriteSuffix P p LP i
  complete t := by
    rcases t with ⟨q, a, b, r, h⟩
    cases h with
    | copyBefore i a hp ha =>
      apply List.mem_flatMap.mpr
      refine ⟨i, LI.complete i, List.mem_append_left _ (List.mem_append_left _ ?_)⟩
      rw [rewritePrefix, dif_pos hp]
      exact List.mem_map.mpr ⟨⟨a, ha⟩, LP.complete ⟨a, ha⟩, rfl⟩
    | one i hp =>
      apply List.mem_flatMap.mpr
      refine ⟨i, LI.complete i, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      unfold rewriteCore
      split
      · simp
      · rename_i a b hsome
        cases hp.symm.trans hsome
    | first i hp =>
      apply List.mem_flatMap.mpr
      refine ⟨i, LI.complete i, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      obtain ⟨⟨a, b⟩, hab⟩ := Option.ne_none_iff_exists.mp hp
      unfold rewriteCore
      split <;> simp_all
    | second i a b hp =>
      apply List.mem_flatMap.mpr
      refine ⟨i, LI.complete i, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      unfold rewriteCore
      split
      · rename_i hnone
        cases hp.symm.trans hnone
      · rename_i a' b' hsome
        have he : (a, b) = (a', b') := Option.some.inj (hp.symm.trans hsome)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simp
    | suffix i a ha =>
      apply List.mem_flatMap.mpr
      refine ⟨i, LI.complete i, List.mem_append_right _ ?_⟩
      exact List.mem_map.mpr ⟨⟨a, ha⟩, LP.complete ⟨a, ha⟩, rfl⟩

def productTransition {Q A P B : Type} {R : Transducer Q A} {S : Transducer P B}
    (r : Transition R) (s : Transition S) : Transition (productTransducer R S) :=
  ⟨(r.source, s.source), (r.input, s.input), (r.output, s.output), (r.target, s.target), ⟨r.allowed, s.allowed⟩⟩

def productListing {Q A P B : Type} {R : Transducer Q A} {S : Transducer P B}
    (LR : Listing (Transition R)) (LS : Listing (Transition S)) :
    Listing (Transition (productTransducer R S)) :=
  (LR.prod LS).map (fun p => productTransition p.1 p.2) (by
    intro t
    exact ⟨(⟨t.source.1, t.input.1, t.output.1, t.target.1, t.allowed.1⟩,
      ⟨t.source.2, t.input.2, t.output.2, t.target.2, t.allowed.2⟩), rfl⟩)

def leftTransition {Q P A : Type} {R : Transducer Q A} (S : Transducer P A)
    (t : Transition R) : Transition (unionTransducer R S) :=
  ⟨.inl t.source, t.input, t.output, .inl t.target, t.allowed⟩

def rightTransition {Q P A : Type} (R : Transducer Q A) {S : Transducer P A}
    (t : Transition S) : Transition (unionTransducer R S) :=
  ⟨.inr t.source, t.input, t.output, .inr t.target, t.allowed⟩

def unionListing {Q P A : Type} {R : Transducer Q A} {S : Transducer P A}
    (LR : Listing (Transition R)) (LS : Listing (Transition S)) :
    Listing (Transition (unionTransducer R S)) :=
  (LR.sum LS).map (fun t => match t with
    | .inl r => leftTransition S r
    | .inr s => rightTransition R s) (by
      intro t
      rcases t with ⟨q, a, b, r, h⟩
      cases q with
      | inl q =>
        cases r with
        | inl r => exact ⟨.inl ⟨q, a, b, r, h⟩, rfl⟩
        | inr r => exact h.elim
      | inr q =>
        cases r with
        | inl r => exact h.elim
        | inr r => exact ⟨.inr ⟨q, a, b, r, h⟩, rfl⟩)

/-- The five reset families are listed, with their actual acceptance proofs. -/
def resetListing {A : Type} (P H : A → Prop) (initial blank : A)
    (LP : Listing {a // P a}) (LH : Listing {a // H a}) :
    Listing (Transition (Reset.transducer P H initial blank)) where
  values :=
    LP.values.flatMap (fun a =>
      [⟨.start, a.val, initial, .before, .firstPlain a.val a.property⟩,
       ⟨.before, a.val, blank, .before, .plainBefore a.val a.property⟩,
       ⟨.after, a.val, blank, .after, .plainAfter a.val a.property⟩]) ++
    LH.values.flatMap (fun a =>
      [⟨.start, a.val, initial, .after, .firstHalt a.val a.property⟩,
       ⟨.before, a.val, blank, .after, .halt a.val a.property⟩])
  complete t := by
    rcases t with ⟨q, a, b, r, h⟩
    cases h with
    | firstPlain a ha =>
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨a, ha⟩, LP.complete ⟨a, ha⟩, by simp⟩)
    | plainBefore a ha =>
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨a, ha⟩, LP.complete ⟨a, ha⟩, by simp⟩)
    | plainAfter a ha =>
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨a, ha⟩, LP.complete ⟨a, ha⟩, by simp⟩)
    | firstHalt a ha =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨a, ha⟩, LH.complete ⟨a, ha⟩, by simp⟩)
    | halt a ha =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨a, ha⟩, LH.complete ⟨a, ha⟩, by simp⟩)

end Medvedev.Domino
