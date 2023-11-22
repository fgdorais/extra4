/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

namespace Prod

def idLeftEquiv (β) : Equiv (PUnit × β) β where
  fwd := Prod.snd
  rev := (PUnit.unit, .)
  fwd_eq_iff_rev_eq := by intro | (PUnit.unit, b), b' => constructor <;> intro | rfl => rfl

def idRightEquiv (α) : Equiv (α × PUnit) α where
  fwd := Prod.fst
  rev := (., PUnit.unit)
  fwd_eq_iff_rev_eq := by intro | (a, PUnit.unit), a' => constructor <;> intro | rfl => rfl

def commEquiv (α β) : Equiv (α × β) (β × α) where
  fwd | (a, b) => (b, a)
  rev | (b, a) => (a, b)
  fwd_eq_iff_rev_eq := by intro | (a, b), (b', a') => constructor <;> intro | rfl => rfl

def assocEquiv (α β γ) : Equiv ((α × β) × γ) (α × (β × γ)) where
  fwd | ((a, b), c) => (a, (b, c))
  rev | (a, (b, c)) => ((a, b), c)
  fwd_eq_iff_rev_eq := by intro | ((a, b), c), (a', (b', c')) => constructor <;> intro | rfl => rfl

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) :
    Equiv (α₁ × β₁) (α₂ × β₂) where
  fwd | (x₁, y₁) => (e.fwd x₁, f.fwd y₁)
  rev | (x₂, y₂) => (e.rev x₂, f.rev y₂)
  fwd_eq_iff_rev_eq := by intro
    | (x₁, y₁), (x₂,y₂) =>
      constructor
      · intro | rfl => ext; exact e.rev_fwd x₁; exact f.rev_fwd y₁
      · intro | rfl => ext; exact e.fwd_rev x₂; exact f.fwd_rev y₂
