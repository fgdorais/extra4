/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

/-- Equivalence of sorts -/
structure Equiv.{u,v} (α : Sort u) (β : Sort v) : Sort (max 1 (max u v)) where
  fwd : α → β
  rev : β → α
  fwd_eq_iff_rev_eq : fwd x = y ↔ rev y = x

namespace Equiv

@[simp] theorem fwd_rev (e : Equiv α β) (x) : e.fwd (e.rev x) = x := by
  rw [Equiv.fwd_eq_iff_rev_eq]

@[simp] theorem rev_fwd (e : Equiv α β) (x) : e.rev (e.fwd x) = x := by
  rw [←Equiv.fwd_eq_iff_rev_eq]

@[simp] theorem comp_fwd_rev (e : Equiv α β) : e.fwd ∘ e.rev = id := funext e.fwd_rev

@[simp] theorem comp_rev_fwd (e : Equiv α β) : e.rev ∘ e.fwd = id := funext e.rev_fwd

@[ext] protected theorem ext {e₁ e₂ : Equiv α β} (h : e₁.fwd = e₂.fwd) : e₁ = e₂ := by
  have h' : e₁.rev = e₂.rev := by funext; rw [← fwd_eq_iff_rev_eq, h, fwd_rev]
  match e₁, e₂ with | ⟨_,_,_⟩, ⟨_,_,_⟩ => cases h; cases h'; rfl

protected theorem ext' {e₁ e₂ : Equiv α β} (h : ∀ x, e₁.fwd x = e₂.fwd x) : e₁ = e₂ := by
  ext; exact h ..

protected def id : Equiv α α where
  fwd := id
  rev := id
  fwd_eq_iff_rev_eq := by intros; constructor <;> intro | rfl => rfl

@[simp] theorem id_fwd (x : α) : Equiv.id.fwd x = x := rfl

@[simp] theorem id_rev (x : α) : Equiv.id.rev x = x := rfl

protected def comp (f : Equiv β γ) (e : Equiv α β) : Equiv α γ where
  fwd := f.fwd ∘ e.fwd
  rev := e.rev ∘ f.rev
  fwd_eq_iff_rev_eq := by
    intros
    simp only [Function.comp]
    constructor
    · intro | rfl => rw [f.rev_fwd, e.rev_fwd]
    · intro | rfl => rw [e.fwd_rev, f.fwd_rev]

@[simp] theorem comp_fwd (f : Equiv β γ) (e : Equiv α β) (x) :
    (Equiv.comp f e).fwd x = f.fwd (e.fwd x) := rfl

@[simp] theorem comp_rev (f : Equiv β γ) (e : Equiv α β) (x) :
    (Equiv.comp f e).rev x = e.rev (f.rev x) := rfl

protected def inv (e : Equiv α β) : Equiv β α where
  fwd := e.rev
  rev := e.fwd
  fwd_eq_iff_rev_eq {x y} := (e.fwd_eq_iff_rev_eq (x:=y) (y:=x)).symm

@[simp] theorem inv_fwd (e : Equiv α β) (x) : (Equiv.inv e).fwd x = e.rev x := rfl

@[simp] theorem inv_rev (e : Equiv α β) (x) : (Equiv.inv e).rev x = e.fwd x := rfl

protected theorem comp_assoc (g : Equiv γ δ) (f : Equiv β γ) (e : Equiv α β) :
    Equiv.comp (Equiv.comp g f) e = Equiv.comp g (Equiv.comp f e) := by ext; rfl

@[simp] protected theorem comp_id_right (e : Equiv α β) : Equiv.comp e Equiv.id = e := by ext; rfl

@[simp] protected theorem comp_id_left (e : Equiv α β) : Equiv.comp e Equiv.id = e := by ext; rfl

@[simp] protected theorem comp_inv_right (e : Equiv α β) :
    Equiv.comp e (Equiv.inv e) = Equiv.id := by ext; simp

@[simp] protected theorem comp_inv_left (e : Equiv α β) :
  Equiv.comp (Equiv.inv e) e = Equiv.id := by ext; simp

@[simp] protected theorem inv_id : Equiv.inv (Equiv.id (α:=α)) = Equiv.id := by ext; rfl

@[simp] protected theorem inv_inv (e : Equiv α β) : Equiv.inv (Equiv.inv e) = e := by ext; rfl

protected theorem inv_comp (f : Equiv β γ) (e : Equiv α β) :
    Equiv.inv (Equiv.comp f e) = Equiv.comp (Equiv.inv e) (Equiv.inv f) := by ext; rfl

def ULift.equiv.{u,v} (α : Type v) : Equiv α (ULift.{u,v} α) where
  fwd := ULift.up
  rev := ULift.down
  fwd_eq_iff_rev_eq := ⟨fun | rfl => rfl, fun | rfl => rfl⟩
