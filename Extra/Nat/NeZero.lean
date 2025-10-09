/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.Lemmas

namespace Nat

def ne_zero (n : Nat) [self : NeZero n] : n ≠ 0 := self.out

def zero_ne (n : Nat) [self : NeZero n] : 0 ≠ n := self.out.symm

def zero_lt (n : Nat) [self : NeZero n] : 0 < n := Nat.zero_lt_of_ne_zero <| ne_zero n

instance (n : Nat) : NeZero (n ^ 0) where
  out := Nat.one_ne_zero
