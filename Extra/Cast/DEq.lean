/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

/-- Dependent equality relation -/
inductive DEq {β : α → Sort _} : {a₁ a₂ : α} → β a₁ → β a₂ → Prop
  /-- Reflexivity for dependent equality -/
  | protected refl (x : β a) : DEq x x

/-- Non-dependent recursor for dependent equality -/
protected def DEq.ndrec {β : α → Sort _} {motive : {a : α} → β a → Prop} {x₁ : β a₁} {x₂ : β a₂} :
    DEq x₁ x₂ → motive x₁ → motive x₂
  | .refl _, h => h

@[match_pattern, inherit_doc DEq.refl]
protected def DEq.rfl {β : α → Sort _} {x : β a} := DEq.refl x

/-- Symmetry for dependent equality -/
protected theorem DEq.symm {β : α → Sort _} {x₁ : β a₁} {x₂ : β a₂} : DEq x₁ x₂ → DEq x₂ x₁
  | .rfl => .rfl

/-- Transitivity for dependent equality -/
protected theorem DEq.trans {β : α → Sort _} {x₁ : β a₁} {x₂ : β a₂} {x₃ : β a₃} :
    DEq x₁ x₂ → DEq x₂ x₃ → DEq x₁ x₃
  | .rfl, .rfl => .rfl

/-- Substitution principle for dependent equality -/
protected theorem DEq.subst {β : α → Sort _} {motive : {a : α} → β a → Prop}
    {x₁ : β a₁} {x₂ : β a₂} : DEq x₁ x₂ → motive x₁ → motive x₂
  | .rfl, h => h

@[inherit_doc DEq.subst]
protected theorem DEq.substr {β : α → Sort _} {motive : {a : α} → β a → Prop}
    {x₁ : β a₁} {x₂ : β a₂} : DEq x₁ x₂ → motive x₂ → motive x₁
  | .rfl, h => h

theorem deq_of_eq {β : α → Sort _} {x₁ x₂ : β a} : x₁ = x₂ → DEq x₁ x₂
  | rfl => .rfl

theorem eq_of_deq {β : α → Sort _} {x₁ x₂ : β a} : DEq x₁ x₂ → x₁ = x₂
  | .rfl => rfl

theorem param_eq_of_deq {β : α → Sort _} {x₁ : β a₁} {x₂ : β a₂} : DEq x₁ x₂ → a₁ = a₂
  | .rfl => rfl

theorem heq_of_deq {β : α → Sort _} {x₁ : β a₁} {x₂ : β a₂} : DEq x₁ x₂ → HEq x₁ x₂
  | .rfl => .rfl

theorem deq_of_heq {β : α → Sort _} {x₁ : β a₁} {x₂ : β a₂} : a₁ = a₂ → DEq x₁ x₂ → HEq x₁ x₂
|  rfl, .rfl => .rfl

/-- Function extensionality for dependent equality -/
protected theorem DEq.funext {β : α → Sort _} {a₁ a₂ : α} {f₁ : β a₁ → γ} {f₂ : β a₂ → γ} :
    a₁ = a₂ → (h : ∀ {x₁ x₂}, DEq x₁ x₂ → f₁ x₁ = f₂ x₂) → DEq (β := fun x => β x → γ) f₁ f₂
  | rfl, h => deq_of_eq <| funext fun _ => h .rfl
