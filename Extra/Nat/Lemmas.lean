/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Nat

theorem add_lt_of_lt_sub' {a b c : Nat} : b < c - a → a + b < c := by
  rw [Nat.add_comm]; exact Nat.add_lt_of_lt_sub

protected theorem le_mul_of_pos_left (m) (h : 0 < n) : m ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.one_mul _).symm) (Nat.mul_le_mul_right _ h)

protected theorem le_mul_of_pos_right (n) (h : 0 < m) : n ≤ n * m :=
  Nat.le_trans (Nat.le_of_eq (Nat.mul_one _).symm) (Nat.mul_le_mul_left _ h)

protected theorem mul_lt_mul_of_lt_of_le (hac : a < c) (hbd : b ≤ d) (hd : 0 < d) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hbd) (Nat.mul_lt_mul_of_pos_right hac hd)

protected theorem mul_lt_mul_of_lt_of_le' (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_lt_of_le hac hbd (Nat.lt_of_lt_of_le hb hbd)

protected theorem mul_lt_mul_of_le_of_lt (hac : a ≤ c) (hbd : b < d) (hc : 0 < c) :
    a * b < c * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hac) (Nat.mul_lt_mul_of_pos_left hbd hc)

protected theorem mul_lt_mul_of_le_of_lt' (hac : a ≤ c) (hbd : b < d) (ha : 0 < a) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt hac hbd (Nat.lt_of_lt_of_le ha hac)

protected theorem mul_lt_mul_of_lt_of_lt {a b c d : Nat} (hac : a < c) (hbd : b < d) :
    a * b < c * d :=
  Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt hac) hbd (Nat.zero_lt_of_lt hac)

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

protected theorem lt_of_mul_lt_mul_left (x : Nat) {y z : Nat} : x * y < x * z → y < z := by
  intro h
  if h' : z ≤ y then
    absurd h
    apply Nat.not_lt_of_ge
    apply Nat.mul_le_mul_left
    exact h'
  else
    apply Nat.lt_of_not_ge
    exact h'

protected theorem lt_of_mul_lt_mul_right (x : Nat) {y z : Nat} : y * x < z * x → y < z := by
  intro h
  if h' : z ≤ y then
    absurd h
    apply Nat.not_lt_of_ge
    apply Nat.mul_le_mul_right
    exact h'
  else
    apply Nat.lt_of_not_ge
    exact h'

protected theorem pow_lt_pow_of_lt_left {a b : Nat} : a < b → {n : Nat} → 0 < n → a ^ n < b ^ n
  | h, n+1, _ => by
    have hpos : 0 < b ^ n := Nat.pos_pow_of_pos n (Nat.zero_lt_of_lt h)
    simp [Nat.pow_succ]
    apply Nat.mul_lt_mul_of_le_of_lt _ h hpos
    exact Nat.pow_le_pow_of_le_left (Nat.le_of_lt h) n

protected theorem pow_lt_pow_of_lt_right {a : Nat} : 1 < a → m < n → a ^ m < a ^ n := by
  intro ha h; induction m, n using Nat.recDiag with try contradiction
  | zero_succ n =>
    have hpos := Nat.pos_pow_of_pos n (Nat.le_of_lt ha)
    apply Nat.lt_of_le_of_lt hpos
    have : a ^ n * 1 < a ^ n * a := Nat.mul_lt_mul_of_pos_left ha hpos
    rwa [Nat.mul_one] at this
  | succ_succ m n ih =>
    apply Nat.mul_lt_mul_of_pos_right _ (Nat.le_of_lt ha)
    exact ih (Nat.lt_of_succ_lt_succ h)

protected theorem pow_le_pow_left {x y : Nat} (h : x ≤ y) (z : Nat) : x ^ z ≤ y ^ z :=
  Nat.pow_le_pow_of_le_left h z

protected theorem pow_le_pow_of_pos_left {x y : Nat} (h : x ≤ y) {z : Nat} : z > 0 → z ^ x ≤ z ^ y :=
  λ hz => Nat.pow_le_pow_of_le_right hz h

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
    · apply Nat.pos_pow_of_pos
      apply Nat.lt_of_le_of_lt
      · apply Nat.zero_le
      · exact h

theorem eq_one_of_mul_eq_one_left (h : m * n = 1) : n = 1 := by
  match n with
  | 0 => contradiction
  | 1 => rfl
  | _+2 =>
    cases m
    · rw [Nat.zero_mul] at h; contradiction
    · rw [Nat.succ_mul] at h; injection h; contradiction

theorem eq_one_of_mul_eq_one_right (h : m * n = 1) : m = 1 := by
  rw [Nat.mul_comm] at h; exact eq_one_of_mul_eq_one_left h

theorem mul_eq_one {m n : Nat} : m * n = 1 ↔ m = 1 ∧ n = 1 := by
  constructor
  · intro h; rw [eq_one_of_mul_eq_one_right h, eq_one_of_mul_eq_one_left h]; trivial
  · intro ⟨hm, hn⟩; rw [hm, hn]

theorem pow_eq_zero {m n : Nat} : m ^ n = 0 ↔ m = 0 ∧ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    rw [Nat.mul_eq_zero]
    constructor
    · intro
      | .inl h =>
        constructor
        · rw [ih] at h; exact h.1
        · exact Nat.succ_ne_zero _
      | .inr h =>
        constructor
        · exact h
        · exact Nat.succ_ne_zero _
    · intro ⟨h, _⟩; exact .inr h

theorem pow_eq_one {m n : Nat} : m ^ n = 1 ↔ m = 1 ∨ n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ]
    rw [Nat.mul_eq_one]
    constructor
    · intro ⟨_, h⟩; exact .inl h
    · intro
      | .inl h =>
        constructor
        · rw [ih]; exact .inl h
        · exact h
