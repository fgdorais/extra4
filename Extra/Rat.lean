/-
Copyright © 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Rat

theorem sub_self (a : Rat) : a - a = 0 := by
  rw [Rat.sub_eq_add_neg, ← normalize_self a]
  simp only [neg_normalize, normalize_add_normalize, normalize_eq_zero]
  rw [Int.neg_mul, Int.add_neg_eq_sub, Int.sub_self]
