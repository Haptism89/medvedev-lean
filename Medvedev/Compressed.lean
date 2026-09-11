import Medvedev.Columns
import Medvedev.ResponseTable
import Mathlib.Tactic.FinCases

/-!
# Section 3: the compressed representatives

`I` and `J` are the two cyclic index types. The successor permutations
are parameters; finite tori are the instance with modular successors.
`Location.seed t` is a genuinely different constructor from an actual
location. This matters even when both periods are one.
-/

namespace Medvedev.Compressed

inductive Marker (I J T : Type) where
  | x : I → Marker I J T
  | y : J → Marker I J T
  | z : Marker I J T
  | seed : T → Marker I J T
  deriving DecidableEq, Fintype

inductive Location (I J T : Type) where
  | actual : I → J → Location I J T
  | seed : T → Location I J T
  deriving DecidableEq, Fintype

inductive State (I J T : Type) where
  | col : I → State I J T
  | colSep : I → State I J T
  | row : J → State I J T
  | rowSep : J → State I J T
  | notNext : Axis → State I J T
  | notSame : Axis → State I J T
  | cell : Location I J T → State I J T
  | source : Axis → Location I J T → State I J T
  | candidate : Axis → Location I J T → State I J T
  | stepH : I → State I J T
  | stepV : J → State I J T
  | expected : Axis → Location I J T → State I J T
  | provider : Key T → State I J T
  deriving DecidableEq, Fintype

variable {I J T : Type} [DecidableEq I] [DecidableEq J] [DecidableEq T]

def tile (τ : I → J → T) : Location I J T → T
  | .actual i j => τ i j
  | .seed t => t

def stateRole (τ : I → J → T) : State I J T → Mid T
  | .col _ => .pos .h
  | .colSep _ => .sep .h
  | .row _ => .pos .v
  | .rowSep _ => .sep .v
  | .notNext a => .notNext a
  | .notSame a => .notSame a
  | .cell l => .cell (tile τ l)
  | .source a l => .source a (tile τ l)
  | .candidate a l => .candidate a (tile τ l)
  | .stepH _ => .step .h
  | .stepV _ => .step .v
  | .expected a l => .expected a (tile τ l)
  | .provider g => .provider g

def cellBlocks (prevI : I → I) (prevJ : J → J) :
    Location I J T → Colour T → Finset (Marker I J T)
  | .seed t, _ => {.seed t}
  | .actual i _, .same .h => {.x i}
  | .actual i _, .next .h => {.x (prevI i), .z}
  | .actual _ j, .same .v => {.y j}
  | .actual _ j, .next .v => {.y (prevJ j), .z}
  | .actual _ _, _ => ∅

/-- All blocklists, including the opposite-axis markers in output seeds.
Values in unsupported columns are immaterial and are set to the empty list
except for copied seed lists. -/
def blocks (prevI : I → I) (prevJ : J → J) (i₀ : I) (j₀ : J) :
    State I J T → Colour T → Finset (Marker I J T)
  | .col i, .same .h => {.x i}
  | .col i, .next .h => {.x (prevI i), .z}
  | .col _, .tag .h => {.z}
  | .colSep i, .same .h => {.x i, .z}
  | .colSep i, .next .h => {.x i}
  | .colSep _, .tag .h => {.z}
  | .row j, .same .v => {.y j}
  | .row j, .next .v => {.y (prevJ j), .z}
  | .row _, .tag .v => {.z}
  | .rowSep j, .same .v => {.y j, .z}
  | .rowSep j, .next .v => {.y j}
  | .rowSep _, .tag .v => {.z}
  | .cell l, c => cellBlocks prevI prevJ l c
  | .source _ _, .key _ | .candidate _ _, .key _ => {.z}
  | .source _ l, c | .candidate _ l, c => cellBlocks prevI prevJ l c
  | .stepH i, .same .h => {.x i, .z}
  | .stepH i, .next .h => {.x i}
  | .stepH _, .key _ => {.z}
  | .stepV j, .same .v => {.y j, .z}
  | .stepV j, .next .v => {.y j}
  | .stepV _, .key _ => {.z}
  | .expected .h (.seed _), _ => {.y j₀}
  | .expected .v (.seed _), _ => {.x i₀}
  | .expected .h (.actual i _), .next .h => {.x i}
  | .expected .h (.actual _ j), .same .v => {.y j}
  | .expected .v (.actual _ j), .next .v => {.y j}
  | .expected .v (.actual i _), .same .h => {.x i}
  | .expected _ (.actual _ _), .key _ => {.z}
  | _, _ => ∅

/-- Equation `eq:compressed-incidence`, literally the supported complements. -/
def representative (τ : I → J → T) (prevI : I → I) (prevJ : J → J) (i₀ : I) (j₀ : J)
    (s : State I J T) : Set (Marker I J T × Colour T) :=
  {p | p.2 ∈ support (stateRole τ s) ∧ p.1 ∉ blocks prevI prevJ i₀ j₀ s p.2}

omit [DecidableEq I] [DecidableEq J] [DecidableEq T] in
theorem roles_surjective (τ : I → J → T) (i₀ : I) (j₀ : J) :
    Function.Surjective (stateRole τ) := by
  intro a
  cases a with
  | pos ax => cases ax; exact ⟨.col i₀, rfl⟩; exact ⟨.row j₀, rfl⟩
  | sep ax => cases ax; exact ⟨.colSep i₀, rfl⟩; exact ⟨.rowSep j₀, rfl⟩
  | notNext ax => exact ⟨.notNext ax, rfl⟩
  | notSame ax => exact ⟨.notSame ax, rfl⟩
  | cell t => exact ⟨.cell (.seed t), rfl⟩
  | source ax t => exact ⟨.source ax (.seed t), rfl⟩
  | candidate ax t => exact ⟨.candidate ax (.seed t), rfl⟩
  | step ax => cases ax; exact ⟨.stepH i₀, rfl⟩; exact ⟨.stepV j₀, rfl⟩
  | expected ax t => exact ⟨.expected ax (.seed t), rfl⟩
  | provider g => exact ⟨.provider g, rfl⟩

end Medvedev.Compressed
