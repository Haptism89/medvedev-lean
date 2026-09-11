import Medvedev.Domino.MachineCode
import Medvedev.Domino.InputLoader

namespace Medvedev.Domino.SerializeMachine

variable {A Q Γ : Type}

/-- Put the designated value at numerical zero. Repeated entries in the
supplied enumeration are harmless; encoding always uses the first occurrence. -/
def encode [DecidableEq A] (L : Listing A) (zero a : A) : Fin (L.values.length + 1) :=
  ⟨(zero :: L.values).idxOf a, by
    simpa using List.idxOf_lt_length_of_mem (List.mem_cons_of_mem zero (L.complete a))⟩

def decode (L : Listing A) (zero : A) (i : Fin (L.values.length + 1)) : A :=
  (zero :: L.values)[i.val]

@[simp] theorem decode_encode [DecidableEq A] (L : Listing A) (zero a : A) :
    decode L zero (encode L zero a) = a := by
  simp [decode, encode]

@[simp] theorem encode_zero [DecidableEq A] (L : Listing A) (zero : A) :
    encode L zero zero = 0 := by
  apply Fin.ext
  simp [encode]

variable [DecidableEq Q] [DecidableEq Γ]

def instruction (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ)
    (t : Q × Γ × Move) : ℕ × ℕ × Move :=
  ((encode LQ M.start t.1).val, (encode LG M.blank t.2.1).val, t.2.2)

/-- A finite row-major numerical table. No choice of encodings or search for
a halting bound occurs: only the supplied finite lists and transitions are used. -/
def code (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : MachineCode where
  states := LQ.values.length
  symbols := LG.values.length
  table := List.ofFn (n := (LQ.values.length + 1) * (LG.values.length + 1)) fun i =>
    let q : Fin (LQ.values.length + 1) :=
      ⟨i.val / (LG.values.length + 1),
        Nat.div_lt_of_lt_mul (i.isLt.trans_eq (Nat.mul_comm _ _))⟩
    let a : Fin (LG.values.length + 1) :=
      ⟨i.val % (LG.values.length + 1), Nat.mod_lt _ (by omega)⟩
    (M.transition (decode LQ M.start q) (decode LG M.blank a)).map (instruction M LQ LG)

theorem row_index_lt {m n : ℕ} (q : Fin (m + 1)) (a : Fin (n + 1)) :
    q.val * (n + 1) + a.val < (m + 1) * (n + 1) := by
  calc
    _ < q.val * (n + 1) + (n + 1) := Nat.add_lt_add_left a.isLt _
    _ = (q.val + 1) * (n + 1) := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (m + 1) * (n + 1) := Nat.mul_le_mul_right _ q.isLt

theorem table_lookup (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ)
    (q : Fin (LQ.values.length + 1)) (a : Fin (LG.values.length + 1)) :
    (code M LQ LG).table.getD (q.val * (LG.values.length + 1) + a.val) none =
      (M.transition (decode LQ M.start q) (decode LG M.blank a)).map (instruction M LQ LG) := by
  rw [List.getD_eq_getElem _ _ (by simpa [code] using row_index_lt q a)]
  simp only [code, List.getElem_ofFn]
  have hq : (q.val * (LG.values.length + 1) + a.val) / (LG.values.length + 1) = q.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt a.isLt]
    omega
  have ha : (q.val * (LG.values.length + 1) + a.val) % (LG.values.length + 1) = a.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]
  simp only [hq, ha]

theorem transition (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) (q : Q) (a : Γ) :
    (code M LQ LG).machine.transition (encode LQ M.start q) (encode LG M.blank a) =
      (M.transition q a).map fun t => (encode LQ M.start t.1, encode LG M.blank t.2.1, t.2.2) := by
  change (match (code M LQ LG).table.getD
      ((encode LQ M.start q).val * (LG.values.length + 1) + (encode LG M.blank a).val) none with
    | none => none
    | some (q', b, m) => if hq : q' < LQ.values.length + 1 then
        if hb : b < LG.values.length + 1 then
          some ((⟨q', hq⟩ : Fin (LQ.values.length + 1)),
            (⟨b, hb⟩ : Fin (LG.values.length + 1)), m) else none
      else none) = _
  rw [table_lookup]
  simp only [decode_encode]
  cases h : M.transition q a with
  | none => rfl
  | some t =>
    simp only [Option.map_some, instruction]
    rw [dif_pos (encode LQ M.start t.1).isLt, dif_pos (encode LG M.blank t.2.1).isLt]

def cfg (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) (c : AbsoluteCfg Q Γ) :
    AbsoluteCfg (Fin (LQ.values.length + 1)) (Fin (LG.values.length + 1)) :=
  ⟨encode LQ M.start c.state, c.head, fun i => encode LG M.blank (c.tape i)⟩

theorem step (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) (c : AbsoluteCfg Q Γ) :
    (code M LQ LG).machine.absoluteStep (cfg M LQ LG c) =
      (M.absoluteStep c).map (cfg M LQ LG) := by
  simp only [Machine.absoluteStep, cfg, transition, Option.map_map]
  congr 1
  funext t
  dsimp only [Function.comp_apply, AbsoluteCfg.after]
  congr 1
  funext i
  by_cases hi : i = c.head <;> simp [Function.update_apply, hi]

theorem respects (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) :
    Turing.Respects M.absoluteStep (code M LQ LG).machine.absoluteStep
      (fun c d => cfg M LQ LG c = d) := by
  rintro c _ rfl
  cases h : M.absoluteStep c with
  | none => simp [step, h]
  | some d => exact ⟨cfg M LQ LG d, rfl, .single (by simp [step, h])⟩

/-- Serialization preserves and reflects blank-tape halting. It does not
assume that an arbitrary numerical state is the first name for its decoded
state: the simulation theorem controls all reachable states instead. -/
theorem halts_iff (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) :
    (code M LQ LG).Halts ↔ M.Halts := by
  rw [MachineCode.Halts, Machine.halts_iff_eval, Machine.halts_iff_eval]
  apply Turing.tr_eval_dom (respects M LQ LG)
  simp [cfg, MachineCode.machine]

end Medvedev.Domino.SerializeMachine
