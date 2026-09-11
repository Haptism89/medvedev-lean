import Medvedev.Semantics
import Medvedev.Lifting

namespace Medvedev.Formula

variable {Atom K W : Type}

/-- Direct-image pullback of atomic valuations. -/
def pullValuation (q : K → W) (v : Atom → Set W → Prop) (p : Atom) (X : Set K) : Prop := v p (q '' X)

theorem pull_persistent (q : K → W) (v : Atom → Set W → Prop) (hv : Persistent v) :
    Persistent (pullValuation q v) := by
  intro p X Y hY hYX hp
  exact hv p _ _ (hY.image q) (Set.image_mono hYX) hp

/-- Forcing commutes with direct images. No surjectivity of q is needed,
because every nonempty subset of q[X] lifts inside X. -/
theorem forces_image (q : K → W) (v : Atom → Set W → Prop) (f : Formula Atom) (X : Set K) :
    Forces (pullValuation q v) X f ↔ Forces v (q '' X) f := by
  induction f generalizing X with
  | atom p => rfl
  | bot => rfl
  | conj f g ihf ihg => exact and_congr (ihf X) (ihg X)
  | disj f g ihf ihg => exact or_congr (ihf X) (ihg X)
  | imp f g ihf ihg =>
    constructor
    · intro h Y hY hYX hf
      let Z := X ∩ q ⁻¹' Y
      have he : q '' Z = Y := image_inter_preimage q X Y hYX
      have hZ : Z.Nonempty := by
        obtain ⟨w, hw⟩ := hY
        obtain ⟨k, hk, rfl⟩ := hYX hw
        exact ⟨k, hk, hw⟩
      have hfZ := (ihf Z).mpr (by rwa [he])
      have hgZ := (ihg Z).mp (h Z hZ Set.inter_subset_left hfZ)
      rwa [he] at hgZ
    · intro h Y hY hYX hf
      exact (ihg Y).mpr (h (q '' Y) (hY.image q) (Set.image_mono hYX) ((ihf Y).mp hf))

end Medvedev.Formula
