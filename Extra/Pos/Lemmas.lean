/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.Lemmas
import Extra.Pos.Basic

namespace Pos

attribute [local induction_eliminator] Pos.recDiag

theorem toNat_one : (1:Pos).toNat = 1 := rfl

theorem toNat_add (x y : Pos) : (x + y).toNat = x.toNat + y.toNat := rfl

theorem toNat_mul (x y : Pos) : (x * y).toNat = x.toNat * y.toNat := rfl

theorem toNat_pow (x : Pos) (y : Nat) : (x ^ y).toNat = x.toNat ^ y := rfl

theorem toNat_eq (x y : Pos) : x = y ↔ x.toNat = y.toNat := ⟨congrArg Pos.toNat, Pos.ext⟩

theorem toNat_ne (x y : Pos) : x ≠ y ↔ x.toNat ≠ y.toNat := not_congr (toNat_eq x y)

theorem toNat_le (x y : Pos) : x ≤ y ↔ x.toNat ≤ y.toNat := Iff.rfl

theorem toNat_ge (x y : Pos) : x ≥ y ↔ x.toNat ≥ y.toNat := Iff.rfl

theorem toNat_lt (x y : Pos) : x < y ↔ x.toNat < y.toNat := Iff.rfl

theorem toNat_gt (x y : Pos) : x > y ↔ x.toNat > y.toNat := Iff.rfl

local macro "by_toNat" : tactic => `(tactic| simp only [toNat_eq, toNat_ge, toNat_gt, toNat_le, toNat_lt, toNat_ne, toNat_one, toNat_add, toNat_mul, toNat_pow])

protected theorem succ_ne_one (x : Pos) : x + 1 ≠ 1 := by
  by_toNat; intro h; absurd (Nat.succ.inj h); exact Nat.ne_zero _

@[simp] protected theorem one_add_eq_add_one (x : Pos) : 1 + x = x + 1 := by
  by_toNat; exact Nat.one_add _

@[simp] protected theorem add_succ (x y : Pos) : x + (y + 1) = (x + y) + 1 := by
  by_toNat; exact Nat.add_succ ..

@[simp] protected theorem succ_add (x y : Pos) : (x + 1) + y = (x + y) + 1 := by
  by_toNat; exact Nat.succ_add ..

protected theorem add_assoc (x y z : Pos) : (x + y) + z = x + (y + z) := by
  by_toNat; exact Nat.add_assoc ..

protected theorem add_comm (x y : Pos) : x + y = y + x := by
  by_toNat; exact Nat.add_comm ..

protected theorem add_left_comm (x y z : Pos) : x + (y + z) = y + (x + z) := by
  by_toNat; exact Nat.add_left_comm ..

protected theorem add_right_comm (x y z : Pos) : (x + y) + z = (x + z) + y := by
  by_toNat; exact Nat.add_right_comm ..

protected theorem add_left_cancel {x y z : Pos} : x + y = x + z → y = z := by
  by_toNat; exact Nat.add_left_cancel

protected theorem add_right_cancel {x y z : Pos} : x + y = z + y → x = z := by
  by_toNat; exact Nat.add_right_cancel

protected theorem ne_add_self_left (x y : Pos) : x ≠ y + x := by
  induction x with
  | one =>
    apply Ne.symm
    exact Pos.succ_ne_one y
  | succ x H =>
    intro h
    rw [Pos.add_succ] at h
    apply H
    exact Pos.add_right_cancel h

protected theorem ne_add_self_right (x y : Pos) : x ≠ x + y := by
  induction x with
  | one =>
    apply Ne.symm
    rw [Pos.one_add_eq_add_one]
    exact Pos.succ_ne_one y
  | succ x H =>
    intro h
    rw [Pos.succ_add] at h
    apply H
    exact Pos.add_right_cancel h

@[simp] protected theorem one_mul (x : Pos) : 1 * x = x := by
  by_toNat; exact Nat.one_mul _

@[simp] protected theorem mul_one (x : Pos) : x * 1 = x := by
  by_toNat; exact Nat.mul_one _

protected theorem succ_mul (x y : Pos) : (x + 1) * y = x * y + y := by
  by_toNat; exact Nat.succ_mul ..

protected theorem mul_succ (x y : Pos) : x * (y + 1) = x * y + x := by
  by_toNat; exact Nat.mul_succ ..

protected theorem mul_assoc (x y z : Pos) : (x * y) * z = x * (y * z) := by
  by_toNat; exact Nat.mul_assoc ..

protected theorem mul_comm (x y : Pos) : x * y = y * x := by
  by_toNat; exact Nat.mul_comm ..

protected theorem mul_left_comm (x y z : Pos) : x * (y * z) = y * (x * z) := by
  by_toNat; exact Nat.mul_left_comm ..

protected theorem mul_right_comm (x y z : Pos) : (x * y) * z = (x * z) * y := by
  by_toNat; exact Nat.mul_right_comm ..

protected theorem left_distrib (x y z : Pos) : x * (y + z) = x * y + x * z := by
  by_toNat; exact Nat.left_distrib ..

protected theorem right_distrib (x y z : Pos) : (x + y) * z = x * z + y * z := by
  by_toNat; exact Nat.right_distrib ..

protected theorem mul_left_cancel {x y z : Pos} : x * y = x * z → y = z := by
  intro h
  induction y, z with
  | one_one => rfl
  | one_succ z _ =>
    rw [Pos.mul_one, Pos.mul_succ] at h
    absurd h
    apply Pos.ne_add_self_left
  | succ_one y _ =>
    rw [Pos.mul_one, Pos.mul_succ] at h
    absurd h.symm
    apply Pos.ne_add_self_left
  | succ_succ y z H =>
    rw [Pos.mul_succ, Pos.mul_succ] at h
    rw [H (Pos.add_right_cancel h)]

protected theorem mul_right_cancel {x y z : Pos} : x * y = z * y → x = z := by
  intro h
  induction x, z with
  | one_one => rfl
  | one_succ x _ =>
    rw [Pos.one_mul, Pos.succ_mul] at h
    absurd h
    apply Pos.ne_add_self_left
  | succ_one z _ =>
    rw [Pos.one_mul, Pos.succ_mul] at h
    absurd h.symm
    apply Pos.ne_add_self_left
  | succ_succ x z H =>
    rw [Pos.succ_mul, Pos.succ_mul] at h
    rw [H (Pos.add_right_cancel h)]

protected theorem pow_zero (x : Pos) : x ^ (0:Nat) = 1 := by
  by_toNat; exact Nat.pow_zero _

protected theorem pow_one (x : Pos) : x ^ (1:Nat) = x := by
  by_toNat; exact Nat.pow_one ..

protected theorem one_pow (x : Nat) : (1 : Pos) ^ x = 1 := by
  by_toNat; exact Nat.one_pow ..

protected theorem pow_succ (x : Pos) (y : Nat) : x ^ (y + 1) = x ^ y * x := by
  by_toNat; exact Nat.pow_succ ..

protected theorem pow_add (x : Pos) (y z : Nat) : x ^ (y + z) = x ^ y * x ^ z := by
  by_toNat; exact Nat.pow_add ..

protected theorem mul_pow (x y : Pos) (z : Nat) : (x * y) ^ z = x ^ z * y ^ z := by
  by_toNat; exact Nat.mul_pow ..

protected theorem pow_mul (x : Pos) (y z : Nat) : x ^ (y * z) = (x ^ y) ^ z := by
  by_toNat; exact Nat.pow_mul ..

protected theorem pow_mul' (x : Pos) (y z : Nat) : x ^ (y * z) = (x ^ z) ^ y := by
  by_toNat; exact Nat.pow_mul' ..

protected theorem pow_assoc (x : Pos) (y z : Nat) : (x ^ y) ^ z = x ^ (y * z) := by
  rw [Pos.pow_mul]

protected theorem le_refl (x : Pos) : x ≤ x := by
  by_toNat; exact Nat.le_refl ..

protected theorem le_trans {x y z : Pos} : x ≤ y → y ≤ z → x ≤ z := by
  by_toNat; exact Nat.le_trans

protected theorem le_antisymm {x y : Pos} : x ≤ y → y ≤ x → x = y := by
  by_toNat; exact Nat.le_antisymm

protected theorem lt_irrefl (x : Pos) : ¬(x < x) := by
  by_toNat; exact Nat.lt_irrefl _

protected theorem lt_trans {x y z : Pos} : x < y → y < z → x < z := by
  by_toNat; exact Nat.lt_trans

protected theorem lt_of_le_of_lt {x y z : Pos} : x ≤ y → y < z → x < z := by
  by_toNat; exact Nat.lt_of_le_of_lt

protected theorem lt_of_lt_of_le {x y z : Pos} : x < y → y ≤ z → x < z := by
  by_toNat; exact Nat.lt_of_lt_of_le

protected theorem le_of_eq {x y : Pos} : x = y → x ≤ y := by
  by_toNat; exact Nat.le_of_eq

protected theorem le_of_lt {x y : Pos} : x < y → x ≤ y := by
  by_toNat; exact Nat.le_of_lt

protected theorem ne_of_lt {x y : Pos} : x < y → x ≠ y := by
  by_toNat; exact Nat.ne_of_lt

protected theorem lt_of_le_of_ne {x y : Pos} : x ≤ y → x ≠ y → x < y := by
  by_toNat; exact Nat.lt_of_le_of_ne

protected theorem le_of_not_gt {x y : Pos} : ¬ x > y → x ≤ y := by
  by_toNat; exact Nat.le_of_not_gt

protected theorem lt_of_not_ge {x y : Pos} : ¬ x ≥ y → x < y := by
  by_toNat; exact Nat.gt_of_not_le

protected theorem not_le_of_gt {x y : Pos} : x > y → ¬ x ≤ y := by
  by_toNat; exact Nat.not_le_of_gt

protected theorem not_lt_of_ge {x y : Pos} : x ≥ y → ¬ x < y := by
  by_toNat; exact Nat.not_lt_of_ge

protected theorem not_le_iff_gt (x y : Pos) : ¬ x ≤ y ↔ x > y :=
  Iff.intro Pos.lt_of_not_ge Pos.not_le_of_gt

protected theorem lt_iff_not_ge (x y : Pos) : x < y ↔ ¬ x ≥ y :=
  Iff.intro Pos.not_le_of_gt Pos.lt_of_not_ge

protected theorem not_lt_iff_ge (x y : Pos) : ¬ x < y ↔ x ≥ y :=
  Iff.intro Pos.le_of_not_gt Pos.not_lt_of_ge

protected theorem le_iff_not_gt (x y : Pos) : x ≤ y ↔ ¬ x > y :=
  Iff.intro Pos.not_lt_of_ge Pos.le_of_not_gt

protected theorem eq_or_lt_of_le {x y : Pos} : x ≤ y → x = y ∨ x < y := by
  by_toNat; exact Nat.eq_or_lt_of_le

protected abbrev le_total (x y : Pos) : x ≤ y ∨ x ≥ y := by
  by_toNat; exact Nat.le_total ..

protected theorem lt_or_ge (x y : Pos) : x < y ∨ x ≥ y := by
  by_toNat; exact Nat.lt_or_ge ..

protected theorem one_le (x : Pos) : 1 ≤ x := by
  by_toNat; apply Nat.succ_le_of_lt; exact Nat.zero_lt _

protected theorem not_lt_one (x : Pos) : ¬(x < 1) := by
  by_toNat; intro h; absurd h; apply Nat.not_lt_of_ge; apply Nat.succ_le_of_lt; exact Nat.zero_lt _

protected theorem one_lt_succ (x : Pos) : 1 < x + 1 := by
  by_toNat; apply Nat.succ_lt_succ; exact Nat.zero_lt _

protected theorem not_succ_le_one (x : Pos) : ¬(x + 1 ≤ 1) := by
  by_toNat; intro h; absurd h; apply Nat.not_le_of_gt; apply Nat.succ_lt_succ; exact Nat.zero_lt _

protected abbrev eq_one_of_le_one {x : Pos} : x ≤ 1 → x = 1 := by
  by_toNat; intro h; apply Nat.le_antisymm; exact h; apply Nat.succ_le_of_lt; exact Nat.zero_lt _

protected theorem le_succ_self (x : Pos) : x ≤ x + 1 := by
  by_toNat; exact Nat.le_add_right ..

protected theorem lt_succ_self (x : Pos) : x < x + 1 := by
  by_toNat; exact Nat.lt_succ_self ..

protected theorem not_succ_le_self (x : Pos) : ¬(x + 1 ≤ x) := by
  by_toNat; exact Nat.not_succ_le_self _

protected theorem not_succ_lt_self (x : Pos) : ¬(x + 1 < x) := by
  by_toNat; apply Nat.not_lt_of_ge; exact Nat.le_add_right ..

protected theorem le_of_lt_succ {x y : Pos} : x < y + 1 → x ≤ y := by
  by_toNat; exact Nat.le_of_lt_succ

protected theorem lt_succ_of_le {x y : Pos} : x ≤ y → x < y + 1 := by
  by_toNat; exact Nat.lt_succ_of_le

protected theorem lt_of_succ_le {x y : Pos} : x + 1 ≤ y → x < y := by
  by_toNat; exact Nat.lt_of_succ_le

protected theorem succ_le_of_lt {x y : Pos} : x < y → x + 1 ≤ y := by
  by_toNat; exact Nat.succ_le_of_lt

protected theorem le_succ_of_le {x y : Pos} : x ≤ y → x ≤ y + 1 := by
  by_toNat; exact Nat.le_succ_of_le

protected theorem le_of_succ_le {x y : Pos} : x + 1 ≤ y → x ≤ y := by
  by_toNat; exact Nat.le_of_succ_le

protected theorem succ_le_succ {x y : Pos} : x ≤ y → x + 1 ≤ y + 1 := by
  by_toNat; exact Nat.succ_le_succ

protected theorem le_of_succ_le_succ {x y : Pos} : x + 1 ≤ y + 1 → x ≤ y := by
  by_toNat; exact Nat.le_of_succ_le_succ

protected theorem succ_lt_succ {x y : Pos} : x < y → x + 1 < y + 1 := by
  by_toNat; exact Nat.succ_lt_succ

protected theorem lt_of_succ_lt_succ {x y : Pos} : x + 1 < y + 1 → x < y := by
  by_toNat; exact Nat.lt_of_succ_lt_succ

protected theorem lt_add_right (x y : Pos) : x < x + y := by
  induction y with
  | one => exact Pos.lt_succ_self x
  | succ y H => apply Pos.lt_trans H; rw [Pos.add_succ]; exact Pos.lt_succ_self (x + y)

protected theorem lt_add_left (x y : Pos) : x < y + x := by
  induction y with
  | one => rw [Pos.one_add_eq_add_one]; exact Pos.lt_succ_self x
  | succ y H => apply Pos.lt_trans H; rw [Pos.succ_add]; exact Pos.lt_succ_self (y + x)

protected theorem add_le_add_left {x y : Pos} : x ≤ y → ∀ z, z + x ≤ z + y := by
  by_toNat; intro h z; apply Nat.add_le_add_left h

protected theorem add_le_add_right {x y : Pos} : x ≤ y → ∀ z, x + z ≤ y + z := by
  by_toNat; intro h z; apply Nat.add_le_add_right h

protected theorem le_of_add_le_add_left {x y z : Pos} : z + x ≤ z + y → x ≤ y := by
  by_toNat; exact Nat.le_of_add_le_add_left

protected theorem le_of_add_le_add_right {x y z : Pos} : x + z ≤ y + z → x ≤ y := by
  by_toNat; exact Nat.le_of_add_le_add_right

protected theorem add_le_add {x₁ y₁ x₂ y₂ : Pos} : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ + x₂ ≤ y₁ + y₂ := by
  by_toNat; exact Nat.add_le_add

protected theorem add_lt_add_left {x y : Pos} : x < y → ∀ z, z + x < z + y := by
  by_toNat; intro h z; apply Nat.add_lt_add_left h

protected theorem add_lt_add_right {x y : Pos} : x < y → ∀ z, x + z < y + z := by
  by_toNat; intro h z; apply Nat.add_lt_add_right h

protected theorem lt_of_add_lt_add_left {x y z : Pos} : z + x < z + y → x < y := by
  by_toNat; exact Nat.lt_of_add_lt_add_left

protected theorem lt_of_add_lt_add_right {x y z : Pos} : x + z < y + z → x < y := by
  by_toNat; exact Nat.lt_of_add_lt_add_right

protected theorem add_lt_add {x₁ y₁ x₂ y₂ : Pos} : x₁ < y₁ → x₂ < y₂ → x₁ + x₂ < y₁ + y₂ := by
  by_toNat; exact Nat.add_lt_add

protected theorem mul_le_mul_left {x y : Pos} : x ≤ y → ∀ z, z * x ≤ z * y := by
  by_toNat; intro h z; apply Nat.mul_le_mul_left _ h

protected theorem mul_le_mul_right {x y : Pos} : x ≤ y → ∀ z, x * z ≤ y * z := by
  by_toNat; intro h z; apply Nat.mul_le_mul_right _ h

protected theorem le_of_mul_le_mul_left {x y z : Pos} : z * x ≤ z * y → x ≤ y := by
  by_toNat; intro h; exact Nat.le_of_mul_le_mul_of_pos_left (Nat.zero_lt _) h

protected theorem le_of_mul_le_mul_right {x y z : Pos} : x * z ≤ y * z → x ≤ y := by
  by_toNat; intro h; exact Nat.le_of_mul_le_mul_of_pos_right (Nat.zero_lt _) h

protected theorem mul_le_mul {x₁ y₁ x₂ y₂ : Pos} : x₁ ≤ y₁ → x₂ ≤ y₂ → x₁ * x₂ ≤ y₁ * y₂ := by
  by_toNat; exact Nat.mul_le_mul

protected theorem mul_lt_mul_left {x y : Pos} : x < y → ∀ z, z * x < z * y := by
  by_toNat; intro h z; apply Nat.mul_lt_mul_of_pos_left h; exact Nat.zero_lt _

protected theorem mul_lt_mul_right {x y : Pos} : x < y → ∀ z, x * z < y * z := by
  by_toNat; intro h z; apply Nat.mul_lt_mul_of_pos_right h; exact Nat.zero_lt _

protected theorem lt_of_mul_lt_mul_left {x y z : Pos} : z * x < z * y → x < y := by
  by_toNat; exact Nat.lt_of_mul_lt_mul_left

protected theorem lt_of_mul_lt_mul_right {x y z : Pos} : x * z < y * z → x < y := by
  by_toNat; exact Nat.lt_of_mul_lt_mul_right

protected theorem mul_lt_mul_of_lt_of_lt {x₁ y₁ x₂ y₂ : Pos} : x₁ < y₁ → x₂ < y₂ → x₁ * x₂ < y₁ * y₂ := by
  by_toNat; exact Nat.mul_lt_mul_of_lt_of_lt

protected theorem pow_le_pow_left {x y : Nat} : x ≤ y → (z : Pos) → z ^ x ≤ z ^ y := by
  by_toNat; intro h z; exact Nat.pow_le_pow_of_pos_left h (Nat.zero_lt z.toNat)

protected theorem pow_le_pow_right {x y : Pos} : x ≤ y → (z : Nat) → x ^ z ≤ y ^ z := by
  by_toNat; exact Nat.pow_le_pow_left

protected theorem pow_lt_pow_of_pos_left {x y : Pos} : x < y → {z : Nat} → z > 0 → x ^ z < y ^ z := by
  by_toNat; exact Nat.pow_lt_pow_of_pos_right

protected theorem lt.dest {x y : Pos} : x < y → ∃ z, x + z = y := by
  intro h
  induction x, y with
  | one_one =>
    absurd h
    exact Pos.not_lt_one 1
  | one_succ y =>
    exists y
    exact Pos.one_add_eq_add_one y
  | succ_one x =>
    absurd h
    exact Pos.not_lt_one (x+1)
  | succ_succ x y ih =>
    match ih (Pos.lt_of_succ_lt_succ h) with
    | ⟨z, hz⟩ =>
      exists z
      rw [Pos.succ_add, hz]

protected theorem lt.intro {x y z : Pos} : x + z = y → x < y := by
  intro h; rw [←h]; exact Pos.lt_add_right x z
