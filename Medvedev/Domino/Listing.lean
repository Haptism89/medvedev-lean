import Medvedev.Domino.MachineWords

namespace Medvedev.Domino

/-- An executable enumeration, with a proof that every element occurs.
Duplicates are permitted. No classical choice of an enumeration is used. -/
structure Listing (A : Type) where
  values : List A
  complete : ∀ a, a ∈ values

namespace Listing

def map {A B : Type} (L : Listing A) (f : A → B) (hf : Function.Surjective f) : Listing B where
  values := L.values.map f
  complete b := by
    obtain ⟨a, rfl⟩ := hf b
    exact List.mem_map.mpr ⟨a, L.complete a, rfl⟩

def prod {A B : Type} (L : Listing A) (K : Listing B) : Listing (A × B) where
  values := L.values.flatMap fun a => K.values.map fun b => (a, b)
  complete ab := List.mem_flatMap.mpr
    ⟨ab.1, L.complete ab.1, List.mem_map.mpr ⟨ab.2, K.complete ab.2, rfl⟩⟩

def sum {A B : Type} (L : Listing A) (K : Listing B) : Listing (A ⊕ B) where
  values := L.values.map Sum.inl ++ K.values.map Sum.inr
  complete a := by
    cases a with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a, L.complete a, rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b, K.complete b, rfl⟩)

def option {A : Type} (L : Listing A) : Listing (Option A) where
  values := none :: L.values.map some
  complete a := by
    cases a with
    | none => exact List.mem_cons_self
    | some a => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, L.complete a, rfl⟩)

def subtype {A : Type} (L : Listing A) (P : A → Prop) [DecidablePred P] : Listing {a // P a} where
  values := L.values.filterMap fun a => if h : P a then some ⟨a, h⟩ else none
  complete a := List.mem_filterMap.mpr ⟨a.val, L.complete a.val, by simp [a.property]⟩

def fin (n : ℕ) : Listing (Fin n) where
  values := List.ofFn id
  complete i := List.mem_ofFn.mpr ⟨i, rfl⟩

def unit : Listing Unit := ⟨[()], by intro a; cases a; simp⟩
def bool : Listing Bool := ⟨[false, true], by intro a; cases a <;> simp⟩
def move : Listing Move := ⟨[.left, .right, .stay], by intro a; cases a <;> simp⟩

def instructions {Q Γ : Type} (LQ : Listing Q) (LG : Listing Γ) : Listing (Instruction Q Γ) :=
  (LQ.prod (LG.prod (LQ.prod (LG.prod move)))).map
    (fun a => ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩)
    (by intro a; exact ⟨(a.state, a.read, a.next, a.write, a.move), rfl⟩)

def rules {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : Listing (Rule M) :=
  (instructions LQ LG).subtype fun r => M.transition r.state r.read = some (r.next, r.write, r.move)

def machinePatterns {Q Γ : Type} [DecidableEq Q] [DecidableEq Γ]
    (M : Machine Q Γ) (LQ : Listing Q) (LG : Listing Γ) : Listing (MachinePattern M) :=
  let L := rules M LQ LG
  let stay := L.subtype fun r => r.val.move = .stay
  let right := L.subtype fun r => r.val.move = .right
  let left := L.subtype fun r => r.val.move = .left
  (stay.sum ((right.prod LG).sum ((left.prod LG).sum left))).map
    (fun i => match i with
      | .inl r => .stay r.val r.property
      | .inr (.inl (r, a)) => .right r.val r.property a
      | .inr (.inr (.inl (r, a))) => .left r.val r.property a
      | .inr (.inr (.inr r)) => .boundary r.val r.property)
    (by
      intro i
      cases i with
      | stay r h => exact ⟨.inl ⟨r, h⟩, rfl⟩
      | right r h a => exact ⟨.inr (.inl (⟨r, h⟩, a)), rfl⟩
      | left r h a => exact ⟨.inr (.inr (.inl (⟨r, h⟩, a))), rfl⟩
      | boundary r h => exact ⟨.inr (.inr (.inr ⟨r, h⟩)), rfl⟩)

end Listing

end Medvedev.Domino
