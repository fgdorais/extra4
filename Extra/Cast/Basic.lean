/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

theorem congr_ndrec {β : α → Sort _} (f : (x : α) → β x → γ) (h : x = x') (y : β x) :
    f x' (Eq.ndrec y h) = f x y := by cases h; rfl

/-- Function extensionality for heterogenous equality -/
protected theorem HEq.funext {β₁ β₂ : α → Sort _} (f₁ : (x : α) → β₁ x) (f₂ : (x : α) → β₂ x)
    (h : ∀ x, HEq (f₁ x) (f₂ x)) : HEq f₁ f₂ := by
  have : β₁ = β₂ := by funext x; exact type_eq_of_heq (h x)
  cases this
  apply heq_of_eq
  funext x
  exact eq_of_heq (h x)
