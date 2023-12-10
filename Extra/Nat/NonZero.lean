/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.Lemmas

namespace Nat

class NonZero (n : Nat) : Prop where
  protected ne_zero : n ≠ 0

def ne_zero (n : Nat) [self : NonZero n] : n ≠ 0 := self.ne_zero

def zero_ne (n : Nat) [self : NonZero n] : 0 ≠ n := Ne.symm self.ne_zero

def zero_lt (n : Nat) [self : NonZero n] : n > 0 := Nat.zero_lt_of_ne_zero self.ne_zero

namespace NonZero

instance (n : Nat) : NonZero (Nat.succ n) where
  ne_zero := Nat.noConfusion

instance (m n : Nat) [NonZero m] : NonZero (m + n) where
  ne_zero h := ne_zero m <| Nat.eq_zero_of_add_eq_zero_right h

instance (m n : Nat) [NonZero n] : NonZero (m + n) where
  ne_zero h := ne_zero n <| Nat.eq_zero_of_add_eq_zero_left h

instance (m n : Nat) [NonZero m] [NonZero n] : NonZero (m * n) where
  ne_zero h := match Nat.mul_eq_zero.mp h with
    | .inl h => ne_zero m h
    | .inr h => ne_zero n h

instance (n : Nat) : NonZero (n ^ 0) where
  ne_zero := Nat.one_ne_zero

instance (m n : Nat) [NonZero m] : NonZero (m ^ n) where
  ne_zero h := ne_zero m (pow_eq_zero.mp h).1
