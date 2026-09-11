import Medvedev.RecognitionForward
import Medvedev.RecognitionReverse
import Medvedev.SemanticsImage
import Medvedev.Construction

namespace Medvedev

open Formula

variable {T K : Type} [DecidableEq T] [Fintype T] [Encodable T] (D : Wang T)
  [DecidableRel D.horizontal] [DecidableRel D.vertical]

/-- Theorem `thm:recognition`, on the original carrier. This even holds
without a finiteness assumption on K; all world quantifiers exclude ∅. -/
theorem recognition : ¬ FrameValid K (alpha D) ↔ Nonempty (Realization D K) := by
  classical
  constructor
  · intro hbad
    simp only [FrameValid, not_forall] at hbad
    obtain ⟨v, hv, X, hX, hfail⟩ := hbad
    obtain ⟨W, hW, _, hGamma, hroot⟩ := (not_forces_imp v X (Gamma D) (.atom .root)).mp hfail
    let w₀ : W := ⟨hW.choose, hW.choose_spec⟩
    let vW := pullValuation (Subtype.val : W → K) v
    have hImage : (Subtype.val : W → K) '' Set.univ = W := by ext k; simp
    have hWne : (Set.univ : Set W).Nonempty := ⟨w₀, Set.mem_univ _⟩
    have hGW : Forces vW Set.univ (Gamma D) :=
      (forces_image (Subtype.val : W → K) v (Gamma D) Set.univ).mpr (by rwa [hImage])
    have hrW : ¬ vW .root Set.univ := by
      change ¬ v .root ((Subtype.val : W → K) '' Set.univ)
      simpa only [hImage] using hroot
    let R := (candidateTraceModel vW (pull_persistent _ v hv)
      ((forces_gamma_iff D vW Set.univ).mp hGW) hWne hrW).realization
    let q (k : K) : W := if hk : k ∈ W then ⟨k, hk⟩ else w₀
    have hq : Function.Surjective q := by
      intro w
      exact ⟨w.val, by simp [q, w.property]⟩
    exact ⟨R.lift q hq⟩
  · rintro ⟨R⟩
    exact R.refutes_alpha

/-- Corollary `cor:recognition-finite`. -/
theorem finite_recognition : FiniteRealizable D ↔ ¬ InML (alpha D) := by
  classical
  constructor
  · rintro ⟨n, ⟨R⟩⟩ hML
    exact R.refutes_alpha (hML n)
  · intro h
    obtain ⟨n, hn⟩ := not_forall.mp h
    exact ⟨n, (recognition D).mp hn⟩

/-- Equation `eq:old-5-6`: the complete internal mathematical reduction,
from directed finite torus tilings to invalidity on finite Medvedev frames. -/
theorem tiling_iff_not_valid : TilesTorus D ↔ ¬ InML (alpha D) :=
  (tilesTorus_iff_finiteRealizable D).trans (finite_recognition D)

end Medvedev
