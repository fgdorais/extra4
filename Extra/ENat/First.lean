import Extra.ENat.Basic
import Extra.ENat.IsFinite

namespace ENat

private def first.leNat (p : Nat → Bool) : Nat → Bool
| 0 => p 0
| x+1 => p (x+1) || leNat p x

def first (p : Nat → Bool) : ENat where
  leNat := first.leNat p
  mono_step := by intro x hx; simp [first.leNat, hx]

theorem first_leNat_of (h : p x) : (first p).leNat x := by
  match x with
  | 0 => exact h
  | x+1 => simp [first, first.leNat, h]

theorem exists_le_first_of_first_leNat (h : (first p).leNat x) : ∃ y, y ≤ x ∧ p y := by
  induction x with
  | zero => exists 0
  | succ x ih =>
    simp [first, first.leNat] at h
    cases h with
    | inl h =>
      exists x+1
      constructor
      · exact Nat.le_refl ..
      · exact h
    | inr h =>
      match ih h with
      | ⟨y, hle, hy⟩ =>
        exists y
        constructor
        · exact Nat.le_trans hle (Nat.le_succ ..)
        · exact hy

@[simp] theorem first_leNat_iff_exists_le (x) : (first p).leNat x ↔ ∃ y, y ≤ x ∧ p y := by
  constructor
  · exact exists_le_first_of_first_leNat
  · intro ⟨y, hle, hy⟩
    apply mono hle
    exact first_leNat_of hy

theorem first_isFinite_of (h : p x) : IsFinite (first p) :=
  ⟨x, first_leNat_of h⟩

theorem first_isFinite_of_exists : (∃ x, p x) → IsFinite (first p)
  | ⟨_, h⟩ => first_isFinite_of h
