import Medvedev.Domino.TransitionListing
import Medvedev.Domino.ClockedMachine
import Medvedev.Domino.ArithmeticBackground
import Medvedev.Domino.Compiler

namespace Medvedev.Domino

instance {Q Γ : Type} [DecidableEq Q] (a : Cell Q Γ) : Decidable (noHead a) :=
  inferInstanceAs (Decidable (a.2 = none))

instance {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ)
    (a : MarkedCell Q Γ) : Decidable (haltCell M a) := by
  cases h : a.1.2 with
  | none => exact isFalse (by simp [haltCell, h])
  | some q =>
    exact decidable_of_iff (M.transition q a.1.1 = none) (by simp [haltCell, h])

def machineTransitionListing {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : Listing (Transition (machineTransducer M)) :=
  rewriteListing noHead machinePattern (Listing.machinePatterns M LQ LG)
    ((LG.prod LQ.option).subtype noHead)

def clockTransitionListing : Listing (Transition Clock.transducer) :=
  rewriteListing (fun b => b = false) Clock.pattern Listing.unit
    (Listing.bool.subtype fun b => b = false)

def resetTransitionListing {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : Listing (Transition (resetTransducer M)) :=
  let letters := (LG.prod LQ.option).prod Listing.bool
  resetListing (fun a : MarkedCell Q Γ => noHead a.1) (haltCell M)
    (headCell M.start M.blank, true) (plain M.blank, false)
    (letters.subtype fun a => noHead a.1) (letters.subtype (haltCell M))

def clockedTransitionListing {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : Listing (Transition (clockedTransducer M)) :=
  unionListing (productListing (machineTransitionListing M LQ LG) clockTransitionListing)
    (resetTransitionListing M LQ LG)

def rawBackgroundListing : Listing ArithmeticBackground.RawTile :=
  (Listing.bool.prod ((Listing.fin 6).prod ((Listing.fin 6).prod ((Listing.fin 6).prod (Listing.fin 6))))).map
    (fun a => ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩)
    (by intro a; exact ⟨(a.double, a.south, a.north, a.west, a.east), rfl⟩)

def backgroundListing : Listing ArithmeticBackground.Tile :=
  rawBackgroundListing.subtype ArithmeticBackground.Balanced

def boardListing {Q A B : Type} {R : Transducer Q A} (LB : Listing B)
    (LT : Listing (Transition R)) : Listing (BoardTile R B) where
  values := .wall :: LB.values.flatMap fun b => LT.values.map fun t => .cell b t
  complete t := by
    cases t with
    | wall => exact List.mem_cons_self
    | cell b t => exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨b, LB.complete b, List.mem_map.mpr ⟨t, LT.complete t, rfl⟩⟩)

instance {I A : Type} (P : A → Prop) (p : I → LocalPattern A) :
    DecidablePred (rewriteTransducer P p).initial := fun _ => inferInstanceAs (Decidable (_ = _))
instance {I A : Type} (P : A → Prop) (p : I → LocalPattern A) :
    DecidablePred (rewriteTransducer P p).final := fun _ => inferInstanceAs (Decidable (_ = _))
instance {A : Type} (P H : A → Prop) (i b : A) :
    DecidablePred (Reset.transducer P H i b).initial := fun _ => inferInstanceAs (Decidable (_ = _))
instance {A : Type} (P H : A → Prop) (i b : A) :
    DecidablePred (Reset.transducer P H i b).final := fun _ => inferInstanceAs (Decidable (_ = _))

instance {Q A P B : Type} (R : Transducer Q A) (S : Transducer P B)
    [DecidablePred R.initial] [DecidablePred S.initial] : DecidablePred (productTransducer R S).initial :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance {Q A P B : Type} (R : Transducer Q A) (S : Transducer P B)
    [DecidablePred R.final] [DecidablePred S.final] : DecidablePred (productTransducer R S).final :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance {Q P A : Type} (R : Transducer Q A) (S : Transducer P A)
    [DecidablePred R.initial] [DecidablePred S.initial] : DecidablePred (unionTransducer R S).initial :=
  fun q => by cases q <;> dsimp [unionTransducer] <;> infer_instance
instance {Q P A : Type} (R : Transducer Q A) (S : Transducer P A)
    [DecidablePred R.final] [DecidablePred S.final] : DecidablePred (unionTransducer R S).final :=
  fun q => by cases q <;> dsimp [unionTransducer] <;> infer_instance

instance {Q Γ : Type} (M : Machine Q Γ) : DecidablePred (clockedTransducer M).initial := by
  unfold clockedTransducer machineTransducer Clock.transducer resetTransducer
  infer_instance

instance {Q Γ : Type} (M : Machine Q Γ) : DecidablePred (clockedTransducer M).final := by
  unfold clockedTransducer machineTransducer Clock.transducer resetTransducer
  infer_instance

instance {Q A B : Type} [DecidableEq Q] (D : Wang B) (R : Transducer Q A)
    [DecidableRel D.horizontal] [DecidablePred R.initial] [DecidablePred R.final] :
    DecidableRel (compile D R).horizontal :=
  fun t u => by cases t <;> cases u <;> dsimp [compile] <;> infer_instance

instance {Q A B : Type} [DecidableEq A] (D : Wang B) (R : Transducer Q A)
    [DecidableRel D.vertical] : DecidableRel (compile D R).vertical :=
  fun t u => by cases t <;> cases u <;> dsimp [compile] <;> infer_instance

end Medvedev.Domino
