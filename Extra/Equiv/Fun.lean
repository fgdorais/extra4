/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic
import Extra.Tactic.Cast

namespace Fun

def equivND {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) : Equiv (α₁ → β₁) (α₂ → β₂) where
  fwd h₁ := f.fwd ∘ h₁ ∘ e.rev
  rev h₂ := f.rev ∘ h₂ ∘ e.fwd
  fwd_eq_iff_rev_eq := by
    intros; constructor
    · intro | rfl => funext; simp only [Function.comp, Equiv.rev_fwd]
    · intro | rfl => funext; simp only [Function.comp, Equiv.fwd_rev]

def equivFst {α₁ α₂} (β : α₁ → Sort _) (e : Equiv α₁ α₂) :
    Equiv ((x₁ : α₁) → β x₁) ((x₂ : α₂) → β (e.rev x₂)) where
  fwd f₁ x₂ := f₁ (e.rev x₂)
  rev f₂ x₁ := e.rev_fwd x₁ ▸ f₂ (e.fwd x₁)
  fwd_eq_iff_rev_eq := by
    intros; constructor
    · intro | rfl => funext; elim_cast; rw [e.rev_fwd]
    · intro | rfl => funext; elim_cast; rw [e.fwd_rev]

def equivSnd {α} {β₁ : α → Sort _} {β₂ : α → Sort _} (e : (x : α) → Equiv (β₁ x) (β₂ x)) :
    Equiv ((x : α) → β₁ x) ((x : α) → β₂ x) where
  fwd f₁ x := (e x).fwd (f₁ x)
  rev f₂ x := (e x).rev (f₂ x)
  fwd_eq_iff_rev_eq := by
    intros; constructor
    · intro | rfl => funext; exact (e _).rev_fwd ..
    · intro | rfl => funext; exact (e _).fwd_rev ..

protected def equiv {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (e : Equiv α₁ α₂)
    (f : (x₁ : α₁) → Equiv (β₁ x₁) (β₂ (e.fwd x₁))) :
      Equiv ((x₁ : α₁) → β₁ x₁) ((x₂ : α₂) → β₂ x₂) :=
  Equiv.comp h3 (Equiv.comp h2 h1) where
  h1 := equivFst β₁ e
  h2 := equivSnd fun x₂ => f (e.rev x₂)
  h3 := {
    rev := fun m x => e.fwd_rev x |>.symm ▸ m x
    fwd := fun n x => e.fwd_rev x ▸ n x
    fwd_eq_iff_rev_eq := by intros; constructor <;> intro | rfl => funext; elim_cast
  }
