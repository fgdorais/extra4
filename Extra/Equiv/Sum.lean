/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

namespace Sum

def idLeftEquiv (β) : Equiv (Sum Empty β) β where
  fwd | inr b => b
  rev := inr
  fwd_eq_iff_rev_eq := by intro | inr b, b' => constructor <;> intro | rfl => rfl

def idRightEquiv (α) : Equiv (Sum α Empty) α where
  fwd | inl a => a
  rev := inl
  fwd_eq_iff_rev_eq := by intro | inl a, a' => constructor <;> intro | rfl => rfl

def commEquiv (α β) : Equiv (Sum α β) (Sum β α) where
  fwd | inl a => inr a | inr b => inl b
  rev | inl b => inr b | inr a => inl a
  fwd_eq_iff_rev_eq := by intro
    | inl _, inl _ => constructor <;> (intro h; cases h)
    | inl a, inr a' => constructor <;> intro | rfl => rfl
    | inr b, inl b' => constructor <;> intro | rfl => rfl
    | inr _, inr _ => constructor <;> (intro h; cases h)

def assocEquiv (α β γ) : Equiv (Sum (Sum α β) γ) (Sum α (Sum β γ)) where
  fwd
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  rev
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c
  fwd_eq_iff_rev_eq := by intro
    | inl (inl a), inl a' => constructor <;> intro | rfl => rfl
    | inl (inl a), inr (inl b') => constructor <;> (intro h; cases h)
    | inl (inl a), inr (inr c') => constructor <;> (intro h; cases h)
    | inl (inr b), inl a' => constructor <;> (intro h; cases h)
    | inl (inr b), inr (inl b') => constructor <;> intro | rfl => rfl
    | inl (inr b), inr (inr c') => constructor <;> (intro h; cases h)
    | inr c, inl a' => constructor <;> (intro h; cases h)
    | inr c, inr (inl b') => constructor <;> (intro h; cases h)
    | inr c, inr (inr c') => constructor <;> intro | rfl => rfl

protected def equiv {α₁ α₂ β₁ β₂} (e : Equiv α₁ α₂) (f : Equiv β₁ β₂) :
    Equiv (Sum α₁ β₁) (Sum α₂ β₂) where
  fwd
  | Sum.inl a₁ => Sum.inl (e.fwd a₁)
  | Sum.inr b₁ => Sum.inr (f.fwd b₁)
  rev
  | Sum.inl a₂ => Sum.inl (e.rev a₂)
  | Sum.inr b₂ => Sum.inr (f.rev b₂)
  fwd_eq_iff_rev_eq := by intro
    | Sum.inl a₁, Sum.inl a₂ =>
      constructor
      · intro | rfl => simp only [e.rev_fwd]
      · intro | rfl => simp only [e.fwd_rev]
    | Sum.inl a₁, Sum.inr b₂ => constructor <;> (intro; contradiction)
    | Sum.inr b₁, Sum.inl a₂ => constructor <;> (intro; contradiction)
    | Sum.inr b₁, Sum.inr b₂ =>
      constructor
      · intro | rfl => simp only [f.rev_fwd]
      · intro | rfl => simp only [f.fwd_rev]
