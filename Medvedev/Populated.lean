import Medvedev.Compressed

namespace Medvedev.Compressed

variable {I J T : Type} [DecidableEq I] [DecidableEq J] [DecidableEq T]

set_option maxHeartbeats 3000000

theorem blocks_card_le_two (pI : I → I) (pJ : J → J) (i₀ : I) (j₀ : J)
    (s : State I J T) (c : Colour T) : (blocks pI pJ i₀ j₀ s c).card ≤ 2 := by
  cases s <;> cases c <;> (try cases_type* Axis Location Key) <;>
    simp [blocks, cellBlocks]

def fourMarkers (i : I) (j : J) (t : T) (k : Fin 4) : Marker I J T :=
  match k.val with
  | 0 => .x i
  | 1 => .y j
  | 2 => .z
  | _ => .seed t

omit [DecidableEq I] [DecidableEq J] [DecidableEq T] in
theorem fourMarkers_injective (i : I) (j : J) (t : T) :
    Function.Injective (fourMarkers i j t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [fourMarkers]

omit [DecidableEq I] [DecidableEq J] [DecidableEq T] in
theorem marker_card_ge_four [Fintype I] [Fintype J] [Fintype T] (i : I) (j : J) (t : T) :
    4 ≤ Fintype.card (Marker I J T) := by
  simpa using Fintype.card_le_of_injective (fourMarkers i j t) (fourMarkers_injective i j t)

/-- Every supported column contains two distinct points, also for one-by-one tori. -/
theorem two_unblocked [Fintype I] [Fintype J] [Fintype T]
    (pI : I → I) (pJ : J → J) (i₀ : I) (j₀ : J) (t₀ : T)
    (s : State I J T) (c : Colour T) :
    ∃ u v : Marker I J T, u ∉ blocks pI pJ i₀ j₀ s c ∧
      v ∉ blocks pI pJ i₀ j₀ s c ∧ u ≠ v := by
  have hm := marker_card_ge_four i₀ j₀ t₀
  have hb := blocks_card_le_two pI pJ i₀ j₀ s c
  have hcard : 1 < (Finset.univ \ blocks pI pJ i₀ j₀ s c).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨u, v, (Finset.mem_sdiff.mp hu).2, (Finset.mem_sdiff.mp hv).2, hne⟩

end Medvedev.Compressed
