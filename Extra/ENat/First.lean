import Extra.ENat.Basic
import Extra.ENat.IsFinite

namespace ENat

private def first.leNat (p : Nat → Bool) : Nat → Bool
| 0 => p 0
| x+1 => p (x+1) || leNat p x

def first (p : Nat → Bool) : ENat where
  leNat := first.leNat p
  leNat_succ := by intro x hx; simp [first.leNat, hx]

theorem first_leNat_of (h : p x) : (first p).leNat x := by
  match x with
  | 0 => exact h
  | x+1 => simp [first, first.leNat, h]

theorem exists_le_of_first_leNat (h : (first p).leNat x) : ∃ y, y ≤ x ∧ p y := by
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
  · exact exists_le_of_first_leNat
  · intro ⟨y, hle, hy⟩
    apply leNat_of_le_of_leNat hle
    exact first_leNat_of hy

theorem first_isFinite_of (h : p x) : IsFinite (first p) :=
  ⟨x, first_leNat_of h⟩

theorem first_isFinite_of_exists : (∃ x, p x) → IsFinite (first p)
  | ⟨_, h⟩ => first_isFinite_of h

theorem toNat_first_le_of (h : p x) (h' := first_isFinite_of h) : (first p).toNat h' ≤ x := by
  rw [← leNat_iff_toNat_le]; exact first_leNat_of h

theorem toNat_first_spec (h : IsFinite (first p)) : p ((first p).toNat h) := by
  have : ((first p).leNat ((first p).toNat h)) := by
    rw [leNat_iff_toNat_le]; exact Nat.le_refl ..
  match exists_le_of_first_leNat this with
  | ⟨x, hle, hx⟩ =>
    match Nat.lt_or_eq_of_le hle with
    | .inr heq => rw [← heq, hx]
    | .inl hlt =>
      absurd Nat.not_le_of_gt hlt
      exact toNat_first_le_of hx
