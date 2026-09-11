import Medvedev.CompressedProperties
import Medvedev.CompressedResponses
import Medvedev.Representatives
import Medvedev.Torus
import Medvedev.Lifting
import Medvedev.Extraction

namespace Medvedev

variable {T : Type} [DecidableEq T] [Fintype T]

/-- Theorem `thm:torus-realization`: all obligations are discharged for the
literal compressed blocklists, including unused tile types. -/
def TorusTiling.realization {D : Wang T} {m n : ℕ} (τ : TorusTiling D m n) :
    Realization D (Compressed.Marker (Fin (m + 1)) (Fin (n + 1)) T × Colour T) := by
  let t₀ := τ.tile 0 0
  let nextI := finRotate (m + 1)
  let nextJ := finRotate (n + 1)
  let prevI := nextI.symm
  let prevJ := nextJ.symm
  apply RepresentativeData.realization
  exact {
    colour := Prod.snd
    colour_surjective := fun c => ⟨(.z, c), rfl⟩
    label := Compressed.stateRole τ.tile
    label_surjective := Compressed.roles_surjective τ.tile 0 0
    set := Compressed.representative τ.tile prevI prevJ 0 0
    set_nontrivial := Compressed.representative_nontrivial τ.tile prevI prevJ 0 0 t₀
    set_proper := Compressed.representative_proper τ.tile prevI prevJ 0 0
    exact_support := Compressed.representative_exact_support τ.tile prevI prevJ 0 0 t₀
    separation := Compressed.representative_separation τ.tile prevI prevJ 0 0 t₀
    response := by
      intro s t hd
      rcases hd with hd | hd
      · obtain ⟨hsub, hs, ht⟩ := Compressed.responseState_correct D τ.tile
          nextI prevI nextJ prevJ 0 0 nextI.symm_apply_apply nextJ.symm_apply_apply
          nextI.apply_symm_apply nextJ.apply_symm_apply τ.horizontal τ.vertical s t hd
        exact ⟨Compressed.responseState nextI nextJ s t, hsub, hs, ht⟩
      · obtain ⟨hsub, ht, hs⟩ := Compressed.responseState_correct D τ.tile
          nextI prevI nextJ prevJ 0 0 nextI.symm_apply_apply nextJ.symm_apply_apply
          nextI.apply_symm_apply nextJ.apply_symm_apply τ.horizontal τ.vertical t s hd
        exact ⟨Compressed.responseState nextI nextJ t s,
          by simpa only [Set.union_comm] using hsub, hs, ht⟩
  }

/-- The complete equivalence of Sections 2 and 3. -/
theorem tilesTorus_iff_finiteRealizable (D : Wang T) : TilesTorus D ↔ FiniteRealizable D := by
  constructor
  · rintro ⟨m, n, ⟨τ⟩⟩
    exact τ.realization.finiteRealizable
  · exact finiteRealizable_tilesTorus D

end Medvedev
