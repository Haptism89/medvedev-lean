import Medvedev.Realization
import Medvedev.ResponseTable

namespace Medvedev

variable {T K : Type} [DecidableEq T] {D : Wang T}

/-- Lemma `lem:response-test`. All three tests follow from H0--H2;
none is an additional condition imposed on a realization. -/
theorem Realization.response_test (R : Realization D K)
    {a b : Mid T} {X Y Z : Set K} {p : Role T}
    (hd : demand D a b) (hX : R.holds X (.mid a)) (hY : R.holds Y (.mid b))
    (hsub : Z ⊆ X ∪ Y) (hZ : R.holds Z p)
    (ha : ¬ Role.mid a ≤ p) (hb : ¬ Role.mid b ≤ p) :
    ∃ d, p = .mid d ∧ Admissible a b d := by
  classical
  cases p with
  | root =>
    obtain ⟨ax, hax, hbx⟩ := demand_omits_step_key hd
    obtain ⟨C, hCZ, hC⟩ := R.back hZ (root_le (.max (.key (.step ax))))
    obtain ⟨k, hk⟩ := R.nonempty hC
    have hc := R.max_colour hC hk
    rcases hsub (hCZ hk) with hkX | hkY
    · exact False.elim (hax (hc ▸ R.mid_colour hX hkX))
    · exact False.elim (hbx (hc ▸ R.mid_colour hY hkY))
  | max c =>
    obtain ⟨k, hk⟩ := R.nonempty hZ
    have hc := R.max_colour hZ hk
    rcases hsub hk with hkX | hkY
    · exact False.elim (ha (hc ▸ R.mid_colour hX hkX))
    · exact False.elim (hb (hc ▸ R.mid_colour hY hkY))
  | mid d =>
    refine ⟨d, rfl, Ne.symm ha, Ne.symm hb, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨k, hk, hkc⟩ := (R.exact_support hZ c).mpr hc
      rcases hsub hk with hkX | hkY
      · exact Or.inl (hkc ▸ R.mid_colour hX hkX)
      · exact Or.inr (hkc ▸ R.mid_colour hY hkY)
    · by_contra hn
      apply hb
      apply R.forth hY hZ
      intro k hk
      rcases hsub hk with hkX | hkY
      · exact False.elim (hn ⟨R.colour k, R.mid_colour hZ hk, R.mid_colour hX hkX⟩)
      · exact hkY
    · by_contra hn
      apply ha
      apply R.forth hX hZ
      intro k hk
      rcases hsub hk with hkX | hkY
      · exact hkX
      · exact False.elim (hn ⟨R.colour k, R.mid_colour hZ hk, R.mid_colour hY hkY⟩)

theorem Realization.respond_admissible (R : Realization D K)
    {a b : Mid T} {X Y : Set K} (hd : demand D a b)
    (hX : R.holds X (.mid a)) (hY : R.holds Y (.mid b)) :
    ∃ Z d, Z ⊆ X ∪ Y ∧ R.holds Z (.mid d) ∧ Admissible a b d := by
  obtain ⟨Z, p, hsub, hZ, ha, hb⟩ := R.respond hd hX hY
  obtain ⟨d, rfl, hadm⟩ := R.response_test hd hX hY hsub hZ ha hb
  exact ⟨Z, d, hsub, hZ, hadm⟩

end Medvedev
