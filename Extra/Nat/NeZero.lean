/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.Lemmas

namespace Nat

def ne_zero (n : Nat) [self : NeZero n] : n ≠ 0 := self.out

def zero_ne (n : Nat) [self : NeZero n] : 0 ≠ n := Ne.symm <| ne_zero n

def zero_lt (n : Nat) [self : NeZero n] : n > 0 := Nat.zero_lt_of_ne_zero <| ne_zero n

instance (m n : Nat) [NeZero m] : NeZero (m + n) where
  out h := ne_zero m (Nat.eq_zero_of_add_eq_zero_right h)

instance (m n : Nat) [NeZero n] : NeZero (m + n) where
  out h := ne_zero n (Nat.eq_zero_of_add_eq_zero_left h)

instance (m n : Nat) [NeZero m] [NeZero n] : NeZero (m * n) where
  out h := match Nat.mul_eq_zero.mp h with
    | .inl h => ne_zero m h
    | .inr h => ne_zero n h

instance (n : Nat) : NeZero (n ^ 0) where
  out := Nat.one_ne_zero

instance (m n : Nat) [NeZero m] : NeZero (m ^ n) where
  out h := ne_zero m (Nat.pow_eq_zero.mp h).1
