/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

def Setoid.map (f : α → β) (s : Setoid β) : Setoid α where
  r x y := s.r (f x) (f y)
  iseqv := by
    constructor
    · intro _; exact Setoid.refl ..
    · intro _ _ h; exact Setoid.symm h
    · intro _ _ _ h₁ h₂; exact Setoid.trans h₁ h₂

instance (f : α → β) (s : Setoid β) [DecidableRel s.r] : DecidableRel (s.map f).r
  | x, y => inferInstanceAs (Decidable (s.r (f x) (f y)))

namespace Quotient

def equiv {α₁ α₂} {s₁ : Setoid α₁} {s₂ : Setoid α₂} (e : Equiv α₁ α₂)
    (H : ∀ x y : α₁, x ≈ y ↔ e.fwd x ≈ e.fwd y) : Equiv (Quotient s₁) (Quotient s₂) where
  fwd x := Quotient.liftOn x (fun x => Quotient.mk s₂ (e.fwd x)) $ by
    intro _ _ h
    apply Quotient.sound
    rw [←H]
    exact h
  rev y := Quotient.liftOn y (fun y => Quotient.mk s₁ (e.rev y)) $ by
    intro _ _ h
    apply Quotient.sound
    rw [H]
    rw [e.fwd_rev, e.fwd_rev]
    exact h
  fwd_eq_iff_rev_eq {x y} := by
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      constructor
      · intro h
        apply Quotient.sound
        rw [H, e.fwd_rev]
        exact Setoid.symm (Quotient.exact h)
      · intro h
        apply Quotient.sound
        rw [←e.fwd_rev y, ←H]
        exact Setoid.symm (Quotient.exact h)
