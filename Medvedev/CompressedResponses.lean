import Medvedev.Compressed

namespace Medvedev.Compressed

variable {I J T : Type} [DecidableEq I] [DecidableEq J] [DecidableEq T]

/-- The displayed D1--D7 response table; only its oriented demanded inputs
are used. The default makes this a total function on all state pairs. -/
def responseState (nextI : I → I) (nextJ : J → J) :
    State I J T → State I J T → State I J T
  | .col i, .notNext .h => .colSep i
  | .colSep i, .notSame .h => .col (nextI i)
  | .row j, .notNext .v => .rowSep j
  | .rowSep j, .notSame .v => .row (nextJ j)
  | .col i, .row j => .cell (.actual i j)
  | .cell l, .provider (.source a _) => .source a l
  | .cell l, .provider (.candidate a _) => .candidate a l
  | .colSep i, .provider (.step .h) => .stepH i
  | .rowSep j, .provider (.step .v) => .stepV j
  | .source .h (.actual i j), .stepH k =>
      if k = i then .expected .h (.actual i j) else .notSame .h
  | .source .v (.actual i j), .stepV k =>
      if k = j then .expected .v (.actual i j) else .notSame .v
  | .source .h (.seed _), .stepH _ => .notSame .h
  | .source .v (.seed _), .stepV _ => .notSame .v
  | .expected .h (.actual i _), .candidate .h (.actual k _) =>
      if k = nextI i then .notSame .v else .notNext .h
  | .expected .v (.actual _ j), .candidate .v (.actual _ l) =>
      if l = nextJ j then .notSame .h else .notNext .v
  | .expected .h _, .candidate .h _ => .notNext .h
  | .expected .v _, .candidate .v _ => .notNext .v
  | _, _ => .notNext .h

set_option maxHeartbeats 15000000
set_option maxRecDepth 4096

/-- Every oriented demanded state pair receives a legal response contained
in its union. Both actual and seed states are universally quantified. -/
theorem responseState_correct (D : Wang T) (τ : I → J → T)
    (nextI prevI : I → I) (nextJ prevJ : J → J) (i₀ : I) (j₀ : J)
    (invI : ∀ i, prevI (nextI i) = i) (invJ : ∀ j, prevJ (nextJ j) = j)
    (revI : ∀ i, nextI (prevI i) = i) (revJ : ∀ j, nextJ (prevJ j) = j)
    (legalH : ∀ i j, D.horizontal (τ i j) (τ (nextI i) j))
    (legalV : ∀ i j, D.vertical (τ i j) (τ i (nextJ j)))
    (s t : State I J T) (hd : OrientedDemand D (stateRole τ s) (stateRole τ t)) :
    let d := responseState nextI nextJ s t
    representative τ prevI prevJ i₀ j₀ d ⊆
      representative τ prevI prevJ i₀ j₀ s ∪ representative τ prevI prevJ i₀ j₀ t ∧
    stateRole τ d ≠ stateRole τ s ∧ stateRole τ d ≠ stateRole τ t := by
  cases s <;> cases t <;> (try cases_type* Axis Location Key) <;>
    simp only [stateRole, tile] at hd <;> cases hd <;>
    simp only [responseState] <;> (try split_ifs) <;>
    simp_all [representative, Set.subset_def, stateRole, tile, support, blocks, cellBlocks,
      Axis.other, Wang.compat, or_imp, forall_and, or_and_right] <;> grind

end Medvedev.Compressed
