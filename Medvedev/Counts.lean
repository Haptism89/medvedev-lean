import Medvedev.Compressed
import Mathlib.Data.Fintype.BigOperators

namespace Medvedev

variable {T : Type} [Fintype T]

@[simp] theorem card_axis : Fintype.card Axis = 2 := by decide

theorem card_key : Fintype.card (Key T) = 4 * Fintype.card T + 2 := by
  rw [← Fintype.card_congr (Key.proxyTypeEquiv T)]
  simp [Fintype.card_sum, Fintype.card_sigma]
  omega

theorem card_colour : Fintype.card (Colour T) = 4 * Fintype.card T + 8 := by
  rw [← Fintype.card_congr (Colour.proxyTypeEquiv T)]
  simp [Fintype.card_sum, card_key]
  omega

theorem card_mid : Fintype.card (Mid T) = 11 * Fintype.card T + 12 := by
  rw [← Fintype.card_congr (Mid.proxyTypeEquiv T)]
  simp [Fintype.card_sum, Fintype.card_sigma, card_key]
  omega

theorem card_role : Fintype.card (Role T) = 15 * Fintype.card T + 21 := by
  rw [← Fintype.card_congr (Role.proxyTypeEquiv T)]
  simp [Fintype.card_sum, card_mid, card_colour]
  omega

theorem card_marker {I J : Type} [Fintype I] [Fintype J] :
    Fintype.card (Compressed.Marker I J T) = Fintype.card I + Fintype.card J + Fintype.card T + 1 := by
  rw [← Fintype.card_congr (Compressed.Marker.proxyTypeEquiv I J T)]
  simp [Fintype.card_sum]
  omega

/-- The boxed carrier bound in Theorem `thm:torus-realization`. -/
theorem compressed_carrier_card {I J : Type} [Fintype I] [Fintype J] :
    Fintype.card (Compressed.Marker I J T × Colour T) =
      (Fintype.card I + Fintype.card J + Fintype.card T + 1) * (4 * Fintype.card T + 8) := by
  rw [Fintype.card_prod, card_marker, card_colour]

end Medvedev
