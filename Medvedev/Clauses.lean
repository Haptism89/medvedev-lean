import Medvedev.Semantics
import Medvedev.DemandCode
import Medvedev.Trace

namespace Medvedev

open Formula

variable {T K : Type} [DecidableEq T] [Fintype T] [Encodable T]

def NFormula : Formula (Role T) := allFinset Finset.univ .atom

def AFormula (p : Role T) : Formula (Role T) :=
  allFinset (Finset.univ.filter (fun q => ¬ p ≤ q)) .atom

def PairFormula (a b : Mid T) : Formula (Role T) :=
  allFinset (Finset.univ.filter (fun q => ¬ Role.mid a ≤ q ∧ ¬ Role.mid b ≤ q)) .atom

def BFormula (p : Role T) : Formula (Role T) := .imp (.imp (AFormula p) (.atom p)) (.atom p)

def SFormula (a b : Mid T) : Formula (Role T) :=
  .imp (PairFormula a b) (.disj (.atom (.mid a)) (.atom (.mid b)))

/-- Section 4's literal four clause families. The two O-families are
separate conjunctions. S uses one orientation of each unordered demand. -/
def Gamma (D : Wang T) [DecidableRel D.horizontal] [DecidableRel D.vertical] : Formula (Role T) :=
  .conj (.imp NFormula .bot)
    (.conj (allFinset Finset.univ (fun a : Mid T => .imp (.atom (.mid a)) (.atom .root)))
      (.conj (allFinset Finset.univ (fun a : Mid T =>
        allFinset (support a) (fun c => .imp (.atom (.max c)) (.atom (.mid a)))))
        (.conj (allFinset (Finset.univ.erase Role.root) BFormula)
          (allFinset Finset.univ (fun a : Mid T =>
            allFinset (Finset.univ.filter (demandCode D a)) (SFormula a))))))

def alpha (D : Wang T) [DecidableRel D.horizontal] [DecidableRel D.vertical] : Formula (Role T) :=
  .imp (Gamma D) (.atom .root)

omit [DecidableEq T] in
@[simp] theorem forces_N (v : Role T → Set K → Prop) (X : Set K) :
    Forces v X NFormula ↔ ∀ p, v p X := by simp [NFormula, Forces]

@[simp] theorem forces_A (v : Role T → Set K → Prop) (X : Set K) (p : Role T) :
    Forces v X (AFormula p) ↔ ∀ q, ¬ p ≤ q → v q X := by simp [AFormula, Forces]

@[simp] theorem forces_pair (v : Role T → Set K → Prop) (X : Set K) (a b : Mid T) :
    Forces v X (PairFormula a b) ↔ ∀ q, ¬ Role.mid a ≤ q → ¬ Role.mid b ≤ q → v q X := by
  simp [PairFormula, Forces]

structure ClauseFacts (D : Wang T) (v : Role T → Set K → Prop) (X : Set K) : Prop where
  N : Forces v X (.imp NFormula .bot)
  Oroot : ∀ a : Mid T, Forces v X (.imp (.atom (.mid a)) (.atom .root))
  Omax : ∀ a c, c ∈ support a → Forces v X (.imp (.atom (.max c)) (.atom (.mid a)))
  B : ∀ p : Role T, p ≠ .root → Forces v X (BFormula p)
  S : ∀ a b, OrientedDemand D a b → Forces v X (SFormula a b)

theorem forces_gamma_iff (D : Wang T) [DecidableRel D.horizontal] [DecidableRel D.vertical]
    (v : Role T → Set K → Prop) (X : Set K) : Forces v X (Gamma D) ↔ ClauseFacts D v X := by
  simp only [Gamma, Forces, forces_allFinset, Finset.mem_univ, true_implies,
    Finset.mem_erase, Finset.mem_filter, and_true, true_and, demandCode_iff]
  constructor
  · rintro ⟨hN, hOroot, hOmax, hB, hS⟩
    exact ⟨hN, hOroot, hOmax, hB, hS⟩
  · intro h
    exact ⟨h.N, h.Oroot, h.Omax, h.B, h.S⟩

end Medvedev
