import Medvedev.Realization

namespace Medvedev

variable {T K W : Type} [DecidableEq T] {D : Wang T}

/-- The image calculation used twice in Lemma `lem:carrier-lifting`. -/
theorem image_inter_preimage (q : K → W) (X : Set K) (C : Set W) (h : C ⊆ q '' X) :
    q '' (X ∩ q ⁻¹' C) = C := by
  ext w
  constructor
  · rintro ⟨k, ⟨hk, hc⟩, rfl⟩
    exact hc
  · intro hw
    obtain ⟨k, hk, rfl⟩ := h hw
    exact ⟨k, ⟨hk, hw⟩, rfl⟩

/-- Lemma `lem:carrier-lifting`, with the pullback witness made explicit. -/
def Realization.lift (R : Realization D W) (q : K → W) (hq : Function.Surjective q) :
    Realization D K where
  holds X p := R.holds (q '' X) p
  nonempty h := by
    obtain ⟨w, k, hk, _⟩ := R.nonempty h
    exact ⟨k, hk⟩
  base := by simpa only [Set.image_univ, Set.range_eq_univ.mpr hq] using R.base
  singleton k := by simpa only [Set.image_singleton] using R.singleton (q k)
  back := by
    intro X p r hX hpr
    obtain ⟨C, hC, hr⟩ := R.back hX hpr
    refine ⟨X ∩ q ⁻¹' C, Set.inter_subset_left, ?_⟩
    rwa [image_inter_preimage q X C hC]
  forth hX hY hsub := R.forth hX hY (Set.image_mono hsub)
  respond := by
    intro a b X Y hd hX hY
    obtain ⟨Z, p, hZ, hp, ha, hb⟩ := R.respond hd hX hY
    have hZ' : Z ⊆ q '' (X ∪ Y) := by simpa only [Set.image_union] using hZ
    refine ⟨(X ∪ Y) ∩ q ⁻¹' Z, p, Set.inter_subset_left, ?_, ha, hb⟩
    rwa [image_inter_preimage q (X ∪ Y) Z hZ']

theorem Realization.finiteRealizable [Fintype K] (R : Realization D K) : FiniteRealizable D := by
  haveI : Nonempty K := ⟨(R.nonempty R.base).choose⟩
  have hcard : 0 < Fintype.card K := Fintype.card_pos
  have hex : ∃ n, Fintype.card K = n + 1 := ⟨Fintype.card K - 1, by omega⟩
  obtain ⟨n, hn⟩ := hex
  let e := (Fintype.equivFin K).symm
  have r := R.lift e e.surjective
  exact ⟨n, ⟨by simpa only [hn] using r⟩⟩

end Medvedev
