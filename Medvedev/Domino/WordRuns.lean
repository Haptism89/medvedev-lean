import Medvedev.Domino.Transducer
import Mathlib.Data.List.OfFn

namespace Medvedev.Domino

/-- The literal left-to-right operational semantics of a transducer. -/
inductive Runs {Q A : Type} (R : Transducer Q A) : Q → List A → List A → Q → Prop
  | nil (q : Q) : Runs R q [] [] q
  | cons {q r s : Q} {a b : A} {u v : List A} :
      R.step q a b r → Runs R r u v s → Runs R q (a :: u) (b :: v) s

namespace Runs

variable {Q A : Type} {R : Transducer Q A}

theorem length_eq {q r : Q} {u v : List A} (h : Runs R q u v r) : u.length = v.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

theorem append {q r s : Q} {u v u' v' : List A}
    (h : Runs R q u v r) (h' : Runs R r u' v' s) : Runs R q (u ++ u') (v ++ v') s := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h (ih h')

theorem of_tiles (w : ℕ) (t : Fin (w + 1) → Transition R)
    (h : ∀ (i : ℕ) (hi : i + 1 < w + 1),
      (t ⟨i, by omega⟩).target = (t ⟨i + 1, hi⟩).source) :
    Runs R (t 0).source (List.ofFn fun i => (t i).input)
      (List.ofFn fun i => (t i).output) (t (Fin.last w)).target := by
  induction w with
  | zero =>
    simpa [List.ofFn_succ] using Runs.cons (t 0).allowed (Runs.nil (R := R) (t 0).target)
  | succ w ih =>
    rw [List.ofFn_succ (f := fun i => (t i).input), List.ofFn_succ (f := fun i => (t i).output)]
    apply Runs.cons (t 0).allowed
    have hh := h 0 (by omega)
    change (t 0).target = (t (0 : Fin (w + 1)).succ).source at hh
    rw [hh]
    exact ih (fun i => t i.succ) (fun i hi => h (i + 1) (by omega))

end Runs

theorem RowRun.runs {Q A : Type} {R : Transducer Q A} {w : ℕ} (r : RowRun R w) :
    Runs R (r.tile 0).source (List.ofFn fun i => (r.tile i).input)
      (List.ofFn fun i => (r.tile i).output) (r.tile (Fin.last w)).target :=
  Runs.of_tiles w r.tile r.horizontal

/-- A state path is an equivalent presentation of operational runs. -/
theorem runs_of_states {Q A : Type} {R : Transducer Q A} (n : ℕ)
    (q : Fin (n + 1) → Q) (u v : Fin n → A)
    (h : ∀ i, R.step (q i.castSucc) (u i) (v i) (q i.succ)) :
    Runs R (q 0) (List.ofFn u) (List.ofFn v) (q (Fin.last n)) := by
  induction n with
  | zero => simpa using Runs.nil (R := R) (q 0)
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact Runs.cons (h 0) (ih (fun i => q i.succ) (fun i => u i.succ)
      (fun i => v i.succ) (fun i => h i.succ))

theorem states_of_runs {Q A : Type} {R : Transducer Q A} {q r : Q} {u v : List A}
    (h : Runs R q u v r) :
    ∃ (n : ℕ) (s : Fin (n + 1) → Q) (a b : Fin n → A),
      List.ofFn a = u ∧ List.ofFn b = v ∧ s 0 = q ∧ s (Fin.last n) = r ∧
      ∀ i, R.step (s i.castSucc) (a i) (b i) (s i.succ) := by
  induction h with
  | nil q =>
    exact ⟨0, fun _ => q, Fin.elim0, Fin.elim0, rfl, rfl, rfl, rfl, fun i => i.elim0⟩
  | @cons q r s x y u v hstep htail ih =>
    obtain ⟨n, qs, a, b, ha, hb, hq, hs, hedge⟩ := ih
    refine ⟨n + 1, Fin.cons q qs, Fin.cons x a, Fin.cons y b, ?_, ?_, rfl, ?_, ?_⟩
    · simpa [List.ofFn_succ] using congrArg (List.cons x) ha
    · simpa [List.ofFn_succ] using congrArg (List.cons y) hb
    · exact hs
    · intro i
      cases i using Fin.cases with
      | zero => simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hq] using hstep
      | succ i => exact hedge i

def Accepts {Q A : Type} (R : Transducer Q A) (u v : List A) : Prop :=
  ∃ q r, R.initial q ∧ R.final r ∧ Runs R q u v r

theorem rowRun_iff_accepts {Q A : Type} {R : Transducer Q A} (w : ℕ) (u v : List A) :
    (∃ r : RowRun R w, List.ofFn (fun i => (r.tile i).input) = u ∧
      List.ofFn (fun i => (r.tile i).output) = v) ↔
    u.length = w + 1 ∧ Accepts R u v := by
  constructor
  · rintro ⟨r, rfl, rfl⟩
    exact ⟨List.length_ofFn, _, _, r.initial, r.final, r.runs⟩
  · rintro ⟨hlen, q, r, hq, hr, hrun⟩
    obtain ⟨n, s, a, b, ha, hb, hs0, hsn, hedge⟩ := states_of_runs hrun
    have hn : n = w + 1 := by simpa only [List.length_ofFn, hlen] using congrArg List.length ha
    subst n
    let tiles : Fin (w + 1) → Transition R := fun i =>
      ⟨s i.castSucc, a i, b i, s i.succ, hedge i⟩
    refine ⟨⟨tiles, ?_, ?_, ?_⟩, ha, hb⟩
    · change R.initial (s 0)
      rwa [hs0]
    · intro i hi
      rfl
    · change R.final (s (Fin.last (w + 1)))
      rwa [hsn]

/-- Literal word semantics for a periodic transducer computation. -/
theorem hasWordCycle_iff {Q A : Type} {R : Transducer Q A} :
    HasWordCycle R ↔ ∃ (n : ℕ) (u : Fin (n + 1) → List A),
      u 0 ≠ [] ∧ ∀ i, Accepts R (u i) (u (finRotate (n + 1) i)) := by
  constructor
  · rintro ⟨w, n, ⟨c⟩⟩
    refine ⟨n, fun j => List.ofFn (fun i => ((c.vertex j).tile i).input), ?_, ?_⟩
    · intro h
      have := congrArg List.length h
      simp at this
    · intro j
      refine ⟨_, _, (c.vertex j).initial, (c.vertex j).final, ?_⟩
      have h := (c.vertex j).runs
      have he : (fun i => ((c.vertex j).tile i).output) =
          (fun i => ((c.vertex (finRotate (n + 1) j)).tile i).input) := funext (c.edge j)
      rwa [he] at h
  · rintro ⟨n, u, hu, h⟩
    have lens (i : Fin (n + 1)) : (u i).length = (u 0).length := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        obtain ⟨q, r, _, _, hrun⟩ := h i.castSucc
        have hh := hrun.length_eq
        have hr : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
        rw [hr] at hh
        exact hh.symm.trans ih
    obtain ⟨w, hw⟩ : ∃ w : ℕ, (u 0).length = w + 1 := by
      have hn : (u 0).length ≠ 0 := by simpa using hu
      exact ⟨(u 0).length - 1, by omega⟩
    have runs : ∀ i, ∃ r : RowRun R w,
        List.ofFn (fun k => (r.tile k).input) = u i ∧
        List.ofFn (fun k => (r.tile k).output) = u (finRotate (n + 1) i) := by
      intro i
      exact (rowRun_iff_accepts w _ _).mpr ⟨(lens i).trans hw, h i⟩
    choose r hr using runs
    refine ⟨w, n, ⟨⟨r, ?_⟩⟩⟩
    intro j i
    have he := List.ofFn_injective ((hr j).2.trans (hr (finRotate (n + 1) j)).1.symm)
    exact congrFun he i

end Medvedev.Domino
