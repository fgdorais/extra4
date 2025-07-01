/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Rat

theorem add_comm (a b : Rat) : a + b = b + a := by
  simp only [add_def]
  ac_rfl

theorem add_zero (a : Rat) : a + 0 = a := by
  simp [add_def, normalize_self]

theorem add_assoc (a b c : Rat) : (a + b) + c = a + (b + c) := by
  rw [← normalize_self a, ← normalize_self b, ← normalize_self c]
  simp only [normalize_add_normalize, Int.add_mul, Int.natCast_mul]
  ac_rfl

theorem mul_assoc (a b c : Rat) : (a * b) * c = a * (b * c) := by
  rw [← normalize_self a, ← normalize_self b, ← normalize_self c]
  simp only [normalize_mul_normalize]
  ac_rfl

theorem add_mul (a b c : Rat) : (a + b) * c = a * c + b * c := by
  rw [← normalize_self a, ← normalize_self b, ← normalize_self c]
  simp only [normalize_add_normalize, normalize_mul_normalize, Int.add_mul, Int.natCast_mul,
    normalize_eq_iff]
  ac_rfl

theorem sub_self (a : Rat) : a - a = 0 := by
  rw [Rat.sub_eq_add_neg, ← normalize_self a]
  simp only [neg_normalize, normalize_add_normalize, normalize_eq_zero]
  rw [Int.neg_mul, Int.add_neg_eq_sub, Int.sub_self]
