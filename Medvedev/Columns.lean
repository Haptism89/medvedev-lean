import Medvedev.Realization

/-! # The set-theoretic blocklist calculation, Lemma `lem:response-columns`. -/

namespace Medvedev

variable {J C : Type}

def columns (S : Set C) (B : C → Set J) : Set (J × C) :=
  {p | p.2 ∈ S ∧ p.1 ∉ B p.2}

/-- This is an exact equivalence, with all three rows of the manuscript's
column test stated explicitly. Populated output columns are essential. -/
theorem response_columns (Sa Sb Sd : Set C) (Ba Bb Bd : C → Set J)
    (populated : ∀ c ∈ Sd, ∃ j, j ∉ Bd c) :
    columns Sd Bd ⊆ columns Sa Ba ∪ columns Sb Bb ↔
    Sd ⊆ Sa ∪ Sb ∧
      (∀ c ∈ Sd, c ∈ Sa → c ∉ Sb → Ba c ⊆ Bd c) ∧
      (∀ c ∈ Sd, c ∉ Sa → c ∈ Sb → Bb c ⊆ Bd c) ∧
      (∀ c ∈ Sd, c ∈ Sa → c ∈ Sb → Ba c ∩ Bb c ⊆ Bd c) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨j, hj⟩ := populated c hc
      rcases h (show (j, c) ∈ columns Sd Bd from ⟨hc, hj⟩) with ha | hb
      · exact Or.inl ha.1
      · exact Or.inr hb.1
    · intro c hc ha hb j hj
      by_contra hn
      rcases h (show (j, c) ∈ columns Sd Bd from ⟨hc, hn⟩) with hja | hjb
      · exact hja.2 hj
      · exact hb hjb.1
    · intro c hc ha hb j hj
      by_contra hn
      rcases h (show (j, c) ∈ columns Sd Bd from ⟨hc, hn⟩) with hja | hjb
      · exact ha hja.1
      · exact hjb.2 hj
    · intro c hc ha hb j hj
      by_contra hn
      rcases h (show (j, c) ∈ columns Sd Bd from ⟨hc, hn⟩) with hja | hjb
      · exact hja.2 hj.1
      · exact hjb.2 hj.2
  · rintro ⟨cover, onlyA, onlyB, both⟩ ⟨j, c⟩ ⟨hc, hj⟩
    by_cases ha : c ∈ Sa <;> by_cases hb : c ∈ Sb
    · by_cases hja : j ∈ Ba c
      · exact Or.inr ⟨hb, fun hjb => hj (both c hc ha hb ⟨hja, hjb⟩)⟩
      · exact Or.inl ⟨ha, hja⟩
    · exact Or.inl ⟨ha, fun hja => hj (onlyA c hc ha hb hja)⟩
    · exact Or.inr ⟨hb, fun hjb => hj (onlyB c hc ha hb hjb)⟩
    · exact False.elim ((cover hc).elim ha hb)

/-- Equation `eq:marker-test`: distinct missing markers fill the column. -/
theorem marker_test (x y : J) :
    (({x} : Set J)ᶜ ∪ ({y} : Set J)ᶜ = Set.univ) ↔ x ≠ y := by
  classical
  constructor
  · intro h he
    subst y
    have : x ∈ (({x} : Set J)ᶜ ∪ ({x} : Set J)ᶜ) := h ▸ Set.mem_univ x
    simp at this
  · intro h
    ext j
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hj : j = x
    · exact Or.inr (fun h' => h (hj.symm.trans h'))
    · exact Or.inl hj

end Medvedev
