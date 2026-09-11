import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Tactic.Tauto
import Aesop

/-!
# Literal definitions from Section 1

The names are constructors, so the disjointness required in Definition
`def:wmpair` is built into the types (due to them being cunstructors). A support is the exact table entry,
not its upward closure. `Role.le` uses the manuscript's role order.
The reverse-inclusion order on worlds is defined separately.
-/

namespace Medvedev

inductive Axis where
  | h | v
  deriving DecidableEq, Fintype, Encodable

def Axis.other : Axis → Axis
  | .h => .v
  | .v => .h

@[simp] theorem Axis.other_other (a : Axis) : a.other.other = a := by cases a <;> rfl
@[simp] theorem Axis.other_ne (a : Axis) : a.other ≠ a := by cases a <;> decide

inductive Key (T : Type) where
  | step : Axis → Key T
  | source : Axis → T → Key T
  | candidate : Axis → T → Key T
  deriving DecidableEq, Fintype, Encodable

inductive Colour (T : Type) where
  | same : Axis → Colour T
  | next : Axis → Colour T
  | tag : Axis → Colour T
  | key : Key T → Colour T
  deriving DecidableEq, Fintype, Encodable

inductive Mid (T : Type) where
  | pos : Axis → Mid T
  | sep : Axis → Mid T
  | notNext : Axis → Mid T
  | notSame : Axis → Mid T
  | cell : T → Mid T
  | source : Axis → T → Mid T
  | candidate : Axis → T → Mid T
  | step : Axis → Mid T
  | expected : Axis → T → Mid T
  | provider : Key T → Mid T
  deriving DecidableEq, Fintype, Encodable

inductive Role (T : Type) where
  | root : Role T
  | mid : Mid T → Role T
  | max : Colour T → Role T
  deriving DecidableEq, Fintype, Encodable

variable {T : Type} [DecidableEq T]

/-- Definition `def:wmpair` (2): exactly the displayed support table. -/
def support : Mid T → Finset (Colour T)
  | .pos a | .sep a => {.same a, .next a, .tag a}
  | .notNext a => {.next a}
  | .notSame a => {.same a}
  | .cell _ => {.same .h, .next .h, .same .v, .next .v}
  | .source a t => {.same a, .same a.other, .key (.source a t)}
  | .candidate a t => {.next a, .same a.other, .key (.candidate a t)}
  | .step a => {.same a, .next a, .key (.step a)}
  | .expected a t => {.next a, .same a.other, .key (.source a t), .key (.step a)}
  | .provider g => {.key g}

/-- The root is least; the only strict remaining comparisons are Mid-to-Max. -/
def Role.le : Role T → Role T → Prop
  | .root, _ => True
  | .mid a, .mid b => a = b
  | .mid a, .max c => c ∈ support a
  | .max c, .max d => c = d
  | _, _ => False

instance : PartialOrder (Role T) where
  le := Role.le
  le_refl p := by cases p <;> simp [Role.le]
  le_trans p q r := by
    intro hpq hqr
    cases p <;> cases q <;> cases r <;> simp_all [Role.le]
  le_antisymm p q := by cases p <;> cases q <;> simp_all [Role.le]

instance : DecidableRel ((· ≤ ·) : Role T → Role T → Prop) := fun p q => by
  change Decidable (Role.le p q)
  cases p <;> cases q <;> dsimp only [Role.le] <;> infer_instance

@[simp] theorem root_le (p : Role T) : Role.root ≤ p := trivial
@[simp] theorem mid_le_mid (a b : Mid T) : Role.mid a ≤ .mid b ↔ a = b := Iff.rfl
@[simp] theorem mid_le_max (a : Mid T) (c : Colour T) :
    Role.mid a ≤ .max c ↔ c ∈ support a := Iff.rfl
@[simp] theorem max_le_max (c d : Colour T) : Role.max c ≤ .max d ↔ c = d := Iff.rfl
@[simp] theorem not_mid_le_root (a : Mid T) : ¬ Role.mid a ≤ .root := id
@[simp] theorem not_max_le_root (c : Colour T) : ¬ Role.max c ≤ .root := id
@[simp] theorem not_max_le_mid (c : Colour T) (a : Mid T) : ¬ Role.max c ≤ .mid a := id

theorem support_nonempty (a : Mid T) : (support a).Nonempty := by
  cases a <;> simp [support]

theorem colour_has_provider (c : Colour T) : ∃ a : Mid T, c ∈ support a := by
  cases c with
  | same a => exact ⟨.notSame a, by simp [support]⟩
  | next a => exact ⟨.notNext a, by simp [support]⟩
  | tag a => exact ⟨.pos a, by simp [support]⟩
  | key g => exact ⟨.provider g, by simp [support]⟩

/-- Definition `def:wang`. Finiteness and nonemptiness of T are separate hypotheses. We do not assume it's finite or non-empty. Slight generalization. -/
structure Wang (T : Type) where
  horizontal : T → T → Prop
  vertical : T → T → Prop

def Wang.compat (D : Wang T) : Axis → T → T → Prop
  | .h => D.horizontal
  | .v => D.vertical

/-- One orientation of D1--D7. `demand` below forgets the orientation. -/
inductive OrientedDemand (D : Wang T) : Mid T → Mid T → Prop
  | generate (a) : OrientedDemand D (.pos a) (.notNext a)
  | separate (a) : OrientedDemand D (.sep a) (.notSame a)
  | cell : OrientedDemand D (.pos .h) (.pos .v)
  | source (a t) : OrientedDemand D (.cell t) (.provider (.source a t))
  | candidate (a t) : OrientedDemand D (.cell t) (.provider (.candidate a t))
  | step (a) : OrientedDemand D (.sep a) (.provider (.step a))
  | expected (a t) : OrientedDemand D (.source a t) (.step a)
  | forbidden (a t u) : ¬ D.compat a t u →
      OrientedDemand D (.expected a t) (.candidate a u)

def demand (D : Wang T) (a b : Mid T) : Prop :=
  OrientedDemand D a b ∨ OrientedDemand D b a

omit [DecidableEq T] in
theorem demand_symm (D : Wang T) (a b : Mid T) : demand D a b ↔ demand D b a := or_comm

omit [DecidableEq T] in
theorem demand_distinct {D : Wang T} {a b : Mid T} (h : demand D a b) : a ≠ b := by
  rcases h with h | h <;> cases h <;> simp

/-- The three checks before Proposition `prop:forced-table`. -/
def Admissible (a b d : Mid T) : Prop :=
  d ≠ a ∧ d ≠ b ∧
  (∀ c ∈ support d, c ∈ support a ∨ c ∈ support b) ∧
  (∃ c, c ∈ support d ∧ c ∈ support a) ∧
  (∃ c, c ∈ support d ∧ c ∈ support b)

theorem admissible_symm (a b d : Mid T) : Admissible a b d ↔ Admissible b a d := by
  unfold Admissible
  simp only [or_comm, and_comm, and_left_comm, and_assoc]

end Medvedev
