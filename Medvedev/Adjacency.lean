import Medvedev.ResponseTest

namespace Medvedev

variable {T K : Type} [DecidableEq T] {D : Wang T}

namespace Realization

variable (R : Realization D K)

def PartIn (X : Set K) (c : Colour T) (Y : Set K) : Prop :=
  ∀ k ∈ X, R.colour k = c → k ∈ Y

theorem part_refl (X : Set K) (c : Colour T) : R.PartIn X c X := fun _ h _ => h

theorem part_empty {X Y : Set K} {a : Mid T} {c : Colour T}
    (hX : R.holds X (.mid a)) (hc : c ∉ support a) : R.PartIn X c Y := by
  intro k hk hkc
  exact False.elim (hc (hkc ▸ R.mid_colour hX hk))

theorem part_union {X Y Z A : Set K} {c : Colour T} (hZ : Z ⊆ X ∪ Y)
    (hX : R.PartIn X c A) (hY : R.PartIn Y c A) : R.PartIn Z c A := by
  intro k hk hkc
  exact (hZ hk).elim (fun h => hX k h hkc) (fun h => hY k h hkc)

theorem part_trans {X Y Z : Set K} {c : Colour T}
    (hXY : R.PartIn X c Y) (hYZ : R.PartIn Y c Z) : R.PartIn X c Z :=
  fun k hk hc => hYZ k (hXY k hk hc) hc

theorem notSame_subset {X Y : Set K} {a : Axis}
    (hX : R.holds X (.mid (.notSame a))) (h : R.PartIn X (.same a) Y) : X ⊆ Y := by
  intro k hk
  apply h k hk
  simpa [support] using R.mid_colour hX hk

theorem notNext_subset {X Y : Set K} {a : Axis}
    (hX : R.holds X (.mid (.notNext a))) (h : R.PartIn X (.next a) Y) : X ⊆ Y := by
  intro k hk
  apply h k hk
  simpa [support] using R.mid_colour hX hk

/-- Both compatibility arguments of Section 2 in one theorem, with the
axis and the directed order of the tile labels explicit. -/
theorem adjacency (ax : Axis) (t u : T) (P Q P' V C C' : Set K)
    (hP : R.holds P (.mid (.pos ax))) (hQ : R.holds Q (.mid (.sep ax)))
    (hP' : R.holds P' (.mid (.pos ax))) (hV : R.holds V (.mid (.pos ax.other)))
    (hC : R.holds C (.mid (.cell t))) (hC' : R.holds C' (.mid (.cell u)))
    (hCV : C ⊆ P ∪ V) (hC'V : C' ⊆ P' ∪ V)
    (hQS : R.PartIn Q (.same ax) P) (hPN : R.PartIn P' (.next ax) Q) :
    D.compat ax t u := by
  have cSame : R.PartIn C (.same ax) P := R.part_union hCV (R.part_refl _ _)
    (R.part_empty hV (by cases ax <;> simp [support, Axis.other]))
  have cOther : R.PartIn C (.same ax.other) V := R.part_union hCV
    (R.part_empty hP (by cases ax <;> simp [support, Axis.other])) (R.part_refl _ _)
  have cNext' : R.PartIn C' (.next ax) Q := R.part_trans
    (R.part_union hC'V (R.part_refl _ _)
      (R.part_empty hV (by cases ax <;> simp [support, Axis.other]))) hPN
  have cOther' : R.PartIn C' (.same ax.other) V := R.part_union hC'V
    (R.part_empty hP' (by cases ax <;> simp [support, Axis.other])) (R.part_refl _ _)
  obtain ⟨F, hF⟩ := R.every_role (.mid (.provider (.source ax t)))
  obtain ⟨L, d, hLC, hL, hd⟩ := R.respond_admissible (Or.inl (.source ax t)) hC hF
  have he := (admissible_source ax t d).mp hd
  subst d
  have lSame : R.PartIn L (.same ax) P := R.part_union hLC cSame
    (R.part_empty hF (by simp [support]))
  have lOther : R.PartIn L (.same ax.other) V := R.part_union hLC cOther
    (R.part_empty hF (by simp [support]))
  obtain ⟨Fs, hFs⟩ := R.every_role (.mid (.provider (.step ax)))
  obtain ⟨U, d, hUQ, hU, hd⟩ := R.respond_admissible (Or.inl (.step ax)) hQ hFs
  have he := (admissible_step ax d).mp hd
  subst d
  have uSame : R.PartIn U (.same ax) P := R.part_union hUQ hQS
    (R.part_empty hFs (by simp [support]))
  have uNext : R.PartIn U (.next ax) Q := R.part_union hUQ (R.part_refl _ _)
    (R.part_empty hFs (by simp [support]))
  obtain ⟨O, d, hOU, hO, hd⟩ := R.respond_admissible (Or.inl (.expected ax t)) hL hU
  rcases (admissible_expected ax t d).mp hd with he | he
  · subst d
    exact False.elim (R.mid_trap hP hO (by simp)
      (R.notSame_subset hO (R.part_union hOU lSame uSame)))
  subst d
  have oNext : R.PartIn O (.next ax) Q := R.part_union hOU
    (R.part_empty hL (by simp [support])) uNext
  have oOther : R.PartIn O (.same ax.other) V := R.part_union hOU lOther
    (R.part_empty hU (by cases ax <;> simp [support, Axis.other]))
  obtain ⟨Fb, hFb⟩ := R.every_role (.mid (.provider (.candidate ax u)))
  obtain ⟨B, d, hBC, hB, hd⟩ := R.respond_admissible (Or.inl (.candidate ax u)) hC' hFb
  have he := (admissible_candidate ax u d).mp hd
  subst d
  have bNext : R.PartIn B (.next ax) Q := R.part_union hBC cNext'
    (R.part_empty hFb (by simp [support]))
  have bOther : R.PartIn B (.same ax.other) V := R.part_union hBC cOther'
    (R.part_empty hFb (by simp [support]))
  by_contra hForbidden
  obtain ⟨Z, d, hZO, hZ, hd⟩ := R.respond_admissible (Or.inl (.forbidden ax t u hForbidden)) hO hB
  rcases (admissible_forbidden ax t u d).mp hd with he | he
  · subst d
    exact R.mid_trap hQ hZ (by simp) (R.notNext_subset hZ (R.part_union hZO oNext bNext))
  · subst d
    exact R.mid_trap hV hZ (by simp) (R.notSame_subset hZ (R.part_union hZO oOther bOther))

end Realization
end Medvedev
