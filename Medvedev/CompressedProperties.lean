import Medvedev.Separation
import Medvedev.Populated

namespace Medvedev.Compressed

variable {I J T : Type} [DecidableEq I] [DecidableEq J] [DecidableEq T]
  [Fintype I] [Fintype J] [Fintype T]

theorem representative_exact_support (τ : I → J → T) (pI : I → I) (pJ : J → J)
    (i₀ : I) (j₀ : J) (t₀ : T) (s : State I J T) (c : Colour T) :
    (∃ k ∈ representative τ pI pJ i₀ j₀ s, k.2 = c) ↔ c ∈ support (stateRole τ s) := by
  constructor
  · rintro ⟨⟨u, d⟩, hk, rfl⟩
    exact hk.1
  · intro hc
    obtain ⟨u, v, hu, _, _⟩ := two_unblocked pI pJ i₀ j₀ t₀ s c
    exact ⟨(u, c), ⟨hc, hu⟩, rfl⟩

theorem representative_nontrivial (τ : I → J → T) (pI : I → I) (pJ : J → J)
    (i₀ : I) (j₀ : J) (t₀ : T) (s : State I J T) :
    (representative τ pI pJ i₀ j₀ s).Nontrivial := by
  obtain ⟨c, hc⟩ := support_nonempty (stateRole τ s)
  obtain ⟨u, v, hu, hv, hne⟩ := two_unblocked pI pJ i₀ j₀ t₀ s c
  exact ⟨(u, c), ⟨hc, hu⟩, (v, c), ⟨hc, hv⟩, fun h => hne (congrArg Prod.fst h)⟩

omit [Fintype T] in
theorem support_omits_tag (a : Mid T) : ∃ ax : Axis, Colour.tag ax ∉ support a := by
  cases a with
  | pos ax => exact ⟨ax.other, by cases ax <;> simp [support, Axis.other]⟩
  | sep ax => exact ⟨ax.other, by cases ax <;> simp [support, Axis.other]⟩
  | _ => exact ⟨.h, by simp [support]⟩

omit [Fintype I] [Fintype J] [Fintype T] in
theorem representative_proper (τ : I → J → T) (pI : I → I) (pJ : J → J)
    (i₀ : I) (j₀ : J) (s : State I J T) :
    ¬ Set.univ ⊆ representative τ pI pJ i₀ j₀ s := by
  obtain ⟨ax, hax⟩ := support_omits_tag (stateRole τ s)
  intro h
  exact hax (h (Set.mem_univ (Marker.x i₀, Colour.tag ax))).1

/-- Lemma `lem:compressed-separation`, in its equivalent contrapositive form. -/
theorem representative_separation (τ : I → J → T) (pI : I → I) (pJ : J → J)
    (i₀ : I) (j₀ : J) (t₀ : T) (s t : State I J T)
    (h : representative τ pI pJ i₀ j₀ s ⊆ representative τ pI pJ i₀ j₀ t) :
    stateRole τ s = stateRole τ t := by
  apply role_eq_of_column_constraints τ pI pJ i₀ j₀ s t
  · intro c hc
    obtain ⟨k, hk, hkc⟩ := (representative_exact_support τ pI pJ i₀ j₀ t₀ s c).mpr hc
    exact hkc ▸ (h hk).1
  · intro c hc u hu
    by_contra hn
    exact (h (show (u, c) ∈ representative τ pI pJ i₀ j₀ s from ⟨hc, hn⟩)).2 hu

end Medvedev.Compressed
