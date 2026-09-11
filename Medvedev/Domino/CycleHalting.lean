import Medvedev.Domino.ClockedMachine

namespace Medvedev.Domino

theorem constant_of_next {A : Type} {n : ℕ} (f : Fin (n + 1) → A)
    (h : ∀ i, f (finRotate (n + 1) i) = f i) (i : Fin (n + 1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hr : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    exact (hr ▸ h i.castSucc).trans ih

theorem no_increasing_cycle {n : ℕ} (f : Fin (n + 1) → ℕ)
    (h : ∀ i, f (finRotate (n + 1) i) = f i + 1) : False := by
  have hf (i : Fin (n + 1)) : f i = f 0 + i.val := by
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have hr : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      have hh := h i.castSucc
      rw [hr, ih] at hh
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using hh
  have hh := h (Fin.last n)
  rw [finRotate_last, hf (Fin.last n)] at hh
  simp only [Fin.val_last] at hh
  omega

/-- A cyclic clocked computation contains a reset, since the non-reset marker
strictly increases. Following the cycle after any reset gives a real initial-to-
halting computation; further resets simply restart that same computation. -/
theorem windowHalts_of_wordCycle {Q Γ : Type} {M : Machine Q Γ}
    (h : HasWordCycle (clockedTransducer M)) : WindowHalts M := by
  classical
  obtain ⟨n, u, _, hedge⟩ := hasWordCycle_iff.mp h
  have lens (i : Fin (n + 1)) : (u i).length = (u 0).length := by
    apply constant_of_next (fun i => (u i).length)
    intro j
    obtain ⟨q, r, _, _, hr⟩ := hedge j
    exact hr.length_eq.symm
  have reset : ∃ i, stoppedWord M ((u i).map Prod.fst) ∧
      u (finRotate (n + 1) i) = markedInitial M ((u i).length - 1) := by
    by_contra hr
    push_neg at hr
    apply no_increasing_cycle (fun i => Clock.rank ((u i).map Prod.snd))
    intro i
    rcases (accepts_clocked_iff M _ _).mp (hedge i) with hn | hs
    · exact Clock.rank_increases hn.2
    · exact (hr i hs.1 hs.2).elim
  obtain ⟨r, hstop, hreset⟩ := reset
  let start := finRotate (n + 1) r
  let w := (u 0).length - 1
  have hstart : u start = markedInitial M w := by simpa [start, w, lens r] using hreset
  have reachable (k : ℕ) : Relation.ReflTransGen (WindowStep M) (initialWord M w)
      ((u (index n (start.val + k))).map Prod.fst) := by
    induction k with
    | zero =>
      simp only [Nat.add_zero, index_coe, hstart, markedInitial_machine]
      exact .refl
    | succ k ih =>
      have hstep := (accepts_clocked_iff M _ _).mp (hedge (index n (start.val + k)))
      rw [← index_succ, Nat.add_assoc] at hstep
      rcases hstep with hn | hs
      · exact ih.tail hn.1
      · rw [hs.2, markedInitial_machine, lens]
  have reachR := reachable (n + 1 + r.val - start.val)
  have coord : start.val + (n + 1 + r.val - start.val) = r.val + (n + 1) := by
    have hs := start.isLt
    omega
  rw [coord, index_add_period, index_coe] at reachR
  exact ⟨w, (u r).map Prod.fst, reachR, hstop⟩

/-- A finite trace explicitly lists its endpoints and every intermediate step. -/
structure FiniteTrace {A : Type} (R : A → A → Prop) (a b : A) where
  length : ℕ
  vertex : Fin (length + 1) → A
  first : vertex 0 = a
  last : vertex (Fin.last length) = b
  edge : ∀ i : Fin length, R (vertex i.castSucc) (vertex i.succ)

theorem trace_of_reachable {A : Type} {R : A → A → Prop} {a b : A}
    (h : Relation.ReflTransGen R a b) : Nonempty (FiniteTrace R a b) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨⟨0, fun _ => b, rfl, rfl, fun i => i.elim0⟩⟩
  | @head a c hstep htail ih =>
    obtain ⟨t⟩ := ih
    refine ⟨⟨t.length + 1, Fin.cons a t.vertex, rfl, t.last, ?_⟩⟩
    intro i
    cases i using Fin.cases with
    | zero => simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, t.first] using hstep
    | succ i => exact t.edge i

theorem WindowStep.pad {Q Γ : Type} {M : Machine Q Γ} {u v : List (Cell Q Γ)}
    (h : WindowStep M u v) (extra : List Γ) :
    WindowStep M (u ++ plainWord extra) (v ++ plainWord extra) := by
  cases h with
  | stay r h l t =>
    simpa [plainWord, List.append_assoc] using WindowStep.stay r h l (t ++ extra)
  | right r h l t a =>
    simpa [plainWord, List.append_assoc] using WindowStep.right r h l (t ++ extra) a
  | left r h l t a =>
    simpa [plainWord, List.append_assoc] using WindowStep.left r h l (t ++ extra) a
  | boundary r h t =>
    simpa [plainWord, List.append_assoc] using WindowStep.boundary r h (t ++ extra)

theorem stoppedWord_pad {Q Γ : Type} {M : Machine Q Γ} {u : List (Cell Q Γ)}
    (h : stoppedWord M u) (extra : List Γ) : stoppedWord M (u ++ plainWord extra) := by
  obtain ⟨l, r, q, a, rfl, hs⟩ := h
  exact ⟨l, r ++ extra, q, a, by simp [plainWord, List.append_assoc], hs⟩

theorem initialWord_pad {Q Γ : Type} (M : Machine Q Γ) (w k : ℕ) :
    initialWord M w ++ plainWord (List.replicate k M.blank) = initialWord M (w + k) := by
  simp [initialWord, plainWord]

/-- Any halting finite computation can be padded with enough blank cells to
carry the advancing marker, then closed by one verified reset row. -/
theorem wordCycle_of_windowHalts {Q Γ : Type} {M : Machine Q Γ}
    (h : WindowHalts M) : HasWordCycle (clockedTransducer M) := by
  obtain ⟨w, u, hreach, hstop⟩ := h
  obtain ⟨t⟩ := trace_of_reachable hreach
  let W := w + t.length
  let p (i : Fin (t.length + 1)) := t.vertex i ++ plainWord (List.replicate t.length M.blank)
  have lengths (i : Fin (t.length + 1)) : (t.vertex i).length = w + 1 := by
    induction i using Fin.induction with
    | zero => rw [t.first]; simp [initialWord, plainWord]
    | succ i ih => exact (t.edge i).length_eq.symm.trans ih
  have plen (i : Fin (t.length + 1)) : (p i).length = W + 1 := by
    simp only [p, List.length_append, plainWord, List.length_map, List.length_replicate, lengths]
    dsimp [W]
    omega
  let clocks (i : Fin (t.length + 1)) := Clock.word i.val (W - i.val)
  have clen (i : Fin (t.length + 1)) : (clocks i).length = W + 1 := by
    rw [Clock.word_length]
    have hi := i.isLt
    dsimp [W]
    omega
  let v (i : Fin (t.length + 1)) := (p i).zip (clocks i)
  have vf (i : Fin (t.length + 1)) : (v i).map Prod.fst = p i :=
    List.map_fst_zip (by rw [plen, clen])
  have vs (i : Fin (t.length + 1)) : (v i).map Prod.snd = clocks i :=
    List.map_snd_zip (by rw [plen, clen])
  have vlen (i : Fin (t.length + 1)) : (v i).length = W + 1 := by
    simpa only [List.length_map, plen] using congrArg List.length (vf i)
  have v0 : v 0 = markedInitial M W := by
    have p0 : p 0 = initialWord M W := by dsimp [p]; rw [t.first, initialWord_pad]
    dsimp [v]
    rw [p0]
    simp [clocks, Clock.word, initialWord, plainWord, markedInitial]
  apply hasWordCycle_iff.mpr
  refine ⟨t.length, v, ?_, ?_⟩
  · rw [v0]
    simp [markedInitial]
  · intro i
    apply (accepts_clocked_iff M _ _).mpr
    by_cases hi : i = Fin.last t.length
    · subst i
      right
      rw [vf, finRotate_last, v0, vlen]
      refine ⟨?_, rfl⟩
      dsimp [p]
      rw [t.last]
      exact stoppedWord_pad hstop _
    · left
      rw [vf, vf, vs, vs]
      have hil : i.val < t.length := by have := i.isLt; simp [Fin.ext_iff] at hi; omega
      let k : Fin t.length := ⟨i.val, hil⟩
      have hk : k.castSucc = i := Fin.ext rfl
      have hks : finRotate (t.length + 1) i = k.succ := finRotate_of_lt hil
      constructor
      · have hp := (t.edge k).pad (List.replicate t.length M.blank)
        rw [hk, ← hks] at hp
        exact hp
      · have hW : i.val < W := by dsimp [W]; omega
        have hval : (finRotate (t.length + 1) i).val = i.val + 1 := by rw [hks]; rfl
        have hclock := Clock.accepts_word i.val (W - i.val - 1)
        change Accepts Clock.transducer (Clock.word i.val (W - i.val))
          (Clock.word (finRotate (t.length + 1) i).val (W - (finRotate (t.length + 1) i).val))
        simpa only [hval, show W - i.val - 1 + 1 = W - i.val by omega,
          show W - (i.val + 1) = W - i.val - 1 by omega] using hclock

theorem clocked_correct {Q Γ : Type} (M : Machine Q Γ) :
    HasWordCycle (clockedTransducer M) ↔ WindowHalts M :=
  ⟨windowHalts_of_wordCycle, wordCycle_of_windowHalts⟩

end Medvedev.Domino
