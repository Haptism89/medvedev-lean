import Medvedev.Semantics

namespace Medvedev.Formula

variable {A B K : Type}

def rename (r : A → B) : Formula A → Formula B
  | .atom a => .atom (r a)
  | .bot => .bot
  | .conj f g => .conj (rename r f) (rename r g)
  | .disj f g => .disj (rename r f) (rename r g)
  | .imp f g => .imp (rename r f) (rename r g)

theorem forces_rename (r : A → B) (v : B → Set K → Prop) (X : Set K) (f : Formula A) :
    Forces v X (rename r f) ↔ Forces (fun a => v (r a)) X f := by
  induction f generalizing X with
  | atom a => rfl
  | bot => rfl
  | conj f g ihf ihg => exact and_congr (ihf X) (ihg X)
  | disj f g ihf ihg => exact or_congr (ihf X) (ihg X)
  | imp f g ihf ihg => simp only [rename, Forces, ihf, ihg]

theorem frameValid_rename_iff (r : A → B) (hr : Function.Injective r) (f : Formula A) :
    FrameValid K (rename r f) ↔ FrameValid K f := by
  constructor
  · intro h v hv X hX
    let w : B → Set K → Prop := fun b Y => ∃ a, r a = b ∧ v a Y
    have hw : Persistent w := by
      rintro b Y Z hZ hZY ⟨a, ha, hvY⟩
      exact ⟨a, ha, hv a Y Z hZ hZY hvY⟩
    have he : (fun a => w (r a)) = v := by
      funext a Y
      apply propext
      constructor
      · rintro ⟨a', ha', hva'⟩
        exact hr ha' ▸ hva'
      · intro hva
        exact ⟨a, rfl, hva⟩
    have hf := (forces_rename r w X f).mp (h w hw X hX)
    rwa [he] at hf
  · intro h v hv X hX
    apply (forces_rename r v X f).mpr
    exact h (fun a => v (r a)) (fun a => hv (r a)) X hX

theorem inML_rename_iff (r : A → B) (hr : Function.Injective r) (f : Formula A) :
    InML (rename r f) ↔ InML f := by
  unfold InML
  exact forall_congr' (fun _ => frameValid_rename_iff r hr f)

end Medvedev.Formula
