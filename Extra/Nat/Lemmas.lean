/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Nat

protected theorem le_of_mul_le_mul_of_pos_left {x y z : Nat} : 0 < x → x * y ≤ x * z → y ≤ z := by
  intro hx hxyz
  if h : z < y then
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_of_pos_left h hx
  else
    exact Nat.le_of_not_gt h

protected theorem le_of_mul_le_mul_of_pos_right {x y z : Nat} : 0 < x → y * x ≤ z * x → y ≤ z := by
  intro hx hxyz
  if h : z < y then
    absurd hxyz
    apply Nat.not_le_of_gt
    exact Nat.mul_lt_mul_of_pos_right h hx
  else
    exact Nat.le_of_not_gt h

protected theorem pow_lt_pow_of_lt_left {a b : Nat} : a < b → {n : Nat} → 0 < n → a ^ n < b ^ n
  | h, n+1, _ => by
    have hpos : 0 < b ^ n := Nat.pow_pos (Nat.zero_lt_of_lt h)
    simp [Nat.pow_succ]
    apply Nat.mul_lt_mul_of_le_of_lt _ h hpos
    exact Nat.pow_le_pow_left (Nat.le_of_lt h) n

protected theorem pow_lt_pow_of_lt_right {a : Nat} : 1 < a → m < n → a ^ m < a ^ n := by
  intro ha h; induction m, n using Nat.recDiag with try contradiction
  | zero_succ n =>
    have hpos : 0 < a^n := Nat.pow_pos (Nat.le_of_lt ha)
    apply Nat.lt_of_le_of_lt hpos
    have : a ^ n * 1 < a ^ n * a := Nat.mul_lt_mul_of_pos_left ha hpos
    rwa [Nat.mul_one] at this
  | succ_succ m n ih =>
    apply Nat.mul_lt_mul_of_pos_right _ (Nat.le_of_lt ha)
    exact ih (Nat.lt_of_succ_lt_succ h)

protected theorem pow_le_pow_of_pos_left {x y : Nat} (h : x ≤ y) {z : Nat} : z > 0 → z ^ x ≤ z ^ y :=
  fun hz => Nat.pow_le_pow_right hz h

protected theorem pow_lt_pow_of_pos_right {x y : Nat} (h : x < y) {z : Nat} : z > 0 → x ^ z < y ^ z := by
  cases z with
  | zero => intro; contradiction
  | succ z =>
    intro
    rw [Nat.pow_succ, Nat.pow_succ]
    apply Nat.mul_lt_mul_of_le_of_lt
    · apply Nat.pow_le_pow_left
      apply Nat.le_of_lt
      exact h
    · exact h
    · apply Nat.pow_pos
      apply Nat.lt_of_le_of_lt
      · apply Nat.zero_le
      · exact h

theorem mul_eq_one {m n : Nat} : m * n = 1 ↔ m = 1 ∧ n = 1 := by
  constructor
  · intro h; rw [eq_one_of_mul_eq_one_right h, eq_one_of_mul_eq_one_left h]; trivial
  · intro ⟨hm, hn⟩; rw [hm, hn]

theorem div_le_of_lt_mul_succ (h : n < k * (m + 1)) : n / k ≤ m := by
  have hk : 0 < k := match k with
    | 0 => by rw [Nat.zero_mul] at h; absurd h; exact Nat.not_lt_zero _
    | _+1 => Nat.zero_lt_succ _
  rw [Nat.mul_comm, ←Nat.div_lt_iff_lt_mul hk] at h
  exact Nat.le_of_lt_succ h

theorem div_le_iff_lt_mul_succ (k0 : 0 < k) : n / k ≤ m ↔ n < k * (m + 1) :=
  ⟨h1, h2⟩
where
  h1 h := by
    rw [←Nat.div_add_mod n k, Nat.mul_succ]
    apply Nat.lt_of_succ_le
    apply Nat.add_le_add _ (Nat.mod_lt _ k0)
    exact Nat.mul_le_mul_left _ h
  h2 h := by
    rw [Nat.mul_comm, ←Nat.div_lt_iff_lt_mul k0] at h
    exact Nat.le_of_lt_succ h
