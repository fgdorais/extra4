/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Int.Basic

namespace Int

attribute [local eliminator] Nat.recDiag

protected theorem sub_eq (i j : Int) : i - j = i + -j := rfl

protected theorem add_add_add_comm (i₁ i₂ j₁ j₂ : Int) : (i₁ + i₂) + (j₁ + j₂) = (i₁ + j₁) + (i₂ + j₂) :=
  calc
  _ = i₁ + (i₂ + (j₁ + j₂)) := by rw [Int.add_assoc]
  _ = i₁ + (j₁ + (i₂ + j₂)) := by rw [Int.add_left_comm i₂ j₁ j₂]
  _ = (i₁ + j₁) + (i₂ + j₂) := by rw [Int.add_assoc]

protected theorem mul_mul_mul_comm (i₁ i₂ j₁ j₂ : Int) : (i₁ * i₂) * (j₁ * j₂) = (i₁ * j₁) * (i₂ * j₂) :=
  calc
  _ = i₁ * (i₂ * (j₁ * j₂)) := by rw [Int.mul_assoc]
  _ = i₁ * (j₁ * (i₂ * j₂)) := by rw [Int.mul_left_comm i₂ j₁ j₂]
  _ = (i₁ * j₁) * (i₂ * j₂) := by rw [Int.mul_assoc]

theorem one_mk_zero : (1 ⊖ 0) = 1 := rfl

theorem mk_self (m) : (m ⊖ m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [succ_mk_succ]; exact ih

theorem add_mk_add_left (k m n) : (k + m ⊖ k + n) = (m ⊖ n) := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ k ih => rw [Nat.succ_add, Nat.succ_add, succ_mk_succ]; exact ih

theorem add_mk_add_right (k m n) : (m + k ⊖ n + k) = (m ⊖ n) := by
  induction k with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ k ih => rw [Nat.add_succ m k, Nat.add_succ n k, succ_mk_succ]; exact ih

theorem mk_add_ofNat (m n k) : (m ⊖ n) + ofNat k = (m + k ⊖ n) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero, Int.zero_add, Nat.zero_add, mk_zero]
  | zero_succ n => rw [zero_mk_succ, Nat.zero_add]; rfl
  | succ_zero m => rw [succ_mk_zero, mk_zero]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, Nat.succ_add, succ_mk_succ, ih]

theorem mk_add_negSucc (m n k) : (m ⊖ n) + negSucc k = (m ⊖ n + k + 1) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero, Int.zero_add, Nat.zero_add]; rfl
  | zero_succ n => rw [zero_mk_succ, zero_mk_succ, Nat.succ_add]; rfl
  | succ_zero m => rw [succ_mk_zero, Nat.zero_add]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, Nat.succ_add, succ_mk_succ]; exact ih

theorem mk_add_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) + (m₂ ⊖ n₂) = (m₁ + m₂ ⊖ n₁ + n₂) := by
  induction m₂, n₂ with
  | zero_zero => rw [zero_mk_zero, Int.add_zero, Nat.add_zero, Nat.add_zero]
  | zero_succ n₂ => rw [zero_mk_succ, Nat.add_succ, mk_add_negSucc]; rfl
  | succ_zero m₂ => rw [mk_zero, mk_add_ofNat]; rfl
  | succ_succ m₂ n₂ ih => rw [succ_mk_succ, Nat.add_succ m₁ m₂, Nat.add_succ n₁ n₂, succ_mk_succ]; exact ih

theorem neg_mk (m n) : -(m ⊖ n) = (n ⊖ m) := by
  induction m, n with
  | zero_zero => rw [zero_mk_zero]; rfl
  | zero_succ n => rw [zero_mk_succ, succ_mk_zero]; rfl
  | succ_zero m => rw [succ_mk_zero, zero_mk_succ]; rfl
  | succ_succ m n ih => rw [succ_mk_succ, succ_mk_succ]; exact ih

theorem mk_sub_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) - (m₂ ⊖ n₂) = (m₁ + n₂ ⊖ n₁ + m₂) :=
  show (m₁ ⊖ n₁) + -(m₂ ⊖ n₂) = (m₁ + n₂ ⊖ n₁ + m₂) by rw [neg_mk, mk_add_mk]

theorem nonNeg_mk (m n) : NonNeg (m ⊖ n) ↔ n ≤ m := by
  induction m, n with
  | zero_zero =>
    rw [zero_mk_zero]
    constructor
    · intro; exact Nat.le_refl ..
    · intro; apply NonNeg.mk
  | zero_succ n =>
    rw [zero_mk_succ]
    constructor
    · intro; contradiction
    · intro; contradiction
  | succ_zero m =>
    rw [succ_mk_zero]
    constructor
    · intro; apply Nat.zero_le
    · intro; apply NonNeg.mk
  | succ_succ m n ih =>
    rw [succ_mk_succ]
    rw [Nat.succ_le_succ_iff]
    exact ih

theorem mk_le_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) ≤ (m₂ ⊖ n₂) ↔ n₂ + m₁ ≤ m₂ + n₁ := by
  simp only [LE.le, Int.le]
  rw [mk_sub_mk, nonNeg_mk]
  rfl

theorem mk_lt_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) < (m₂ ⊖ n₂) ↔ n₂ + m₁ < m₂ + n₁ := by
  simp only [LT.lt, Int.lt, Nat.lt]
  rw [←one_mk_zero, mk_add_mk, mk_le_mk, Nat.add_succ, Nat.add_zero]
  rfl

protected theorem add_neg_self_left (i : Int) : -i + i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem add_neg_self_right (i : Int) : i + -i = 0 := by
  cases i using Int.casesMkOn with
  | mk mi ni => rw [neg_mk, mk_add_mk, Nat.add_comm mi ni, mk_self]

protected theorem sub_add_assoc (i j k : Int) : (i - j) + k = i - (j - k) :=
  calc
  _ = (i + -j) + k := by rw [Int.sub_eq]
  _ = i + (-j + k) := by rw [Int.add_assoc]
  _ = i + (-j + -(-k)) := by rw [Int.neg_neg]
  _ = i + -(j + -k) := by rw [Int.neg_add]
  _ = i - (j - k) := by rw [Int.sub_eq, Int.sub_eq]

theorem mk_mul_ofNat (m n k) : (m ⊖ n) * ofNat k = (m * k ⊖ n * k) := by
  induction m, n with
  | zero_zero => rw [Nat.zero_mul, zero_mk_zero, Int.zero_mul]
  | zero_succ n => rw [Nat.zero_mul, zero_mk, zero_mk]; rfl
  | succ_zero m => rw [Nat.zero_mul, mk_zero, mk_zero]; rfl
  | succ_succ m n ih => rw [Nat.succ_mul, Nat.succ_mul, succ_mk_succ, add_mk_add_right]; exact ih

theorem mk_mul_negSucc (m n k) : (m ⊖ n) * negSucc k = (n * (k + 1) ⊖ m * (k + 1)) := by
  induction m, n with
  | zero_zero => rw [Nat.zero_mul, zero_mk_zero, Int.zero_mul]
  | zero_succ n => rw [Nat.zero_mul, zero_mk, mk_zero]; rfl
  | succ_zero m => rw [Nat.zero_mul, mk_zero, zero_mk]; rfl
  | succ_succ m n ih => rw [Nat.succ_mul, Nat.succ_mul, succ_mk_succ, add_mk_add_right]; exact ih

theorem mk_mul_mk (m₁ n₁ m₂ n₂) : (m₁ ⊖ n₁) * (m₂ ⊖ n₂) = (m₁ * m₂ + n₁ * n₂ ⊖ m₁ * n₂ + n₁ * m₂) := by
  induction m₂, n₂ with
  | zero_zero => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, zero_mk_zero, Int.mul_zero]
  | zero_succ n₂ => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, zero_mk_succ, mk_mul_negSucc]
  | succ_zero m₂ => simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add, succ_mk_zero, mk_mul_ofNat, Nat.mul_comm]
  | succ_succ m₂ n₂ ih => simp only [Nat.mul_succ, Nat.succ_mul]; rw [succ_mk_succ, Nat.add_add_add_comm _ m₁ _ n₁, Nat.add_add_add_comm _ m₁ _ n₁, add_mk_add_right]; exact ih
