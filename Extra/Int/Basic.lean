/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Int

protected alias mk := Int.subNatNat

scoped infix:55 " ⊖ " => Int.mk

@[simp] theorem zero_mk_zero : 0 ⊖ 0 = 0 := rfl

theorem zero_mk_succ (n) : (0 ⊖ n + 1) = Int.negSucc n := rfl

theorem succ_mk_zero (m) : (m + 1 ⊖ 0) = Int.ofNat (m+1) := by
  rw [Int.mk, Int.subNatNat, Nat.zero_sub, Nat.sub_zero]

theorem succ_mk_succ (m n) : (m + 1 ⊖ n + 1) = (m ⊖ n) := by
  rw [Int.mk, Int.subNatNat, Int.subNatNat, Nat.succ_sub_succ, Nat.succ_sub_succ]

@[simp] theorem mk_zero (m) : (m ⊖ 0) = ofNat m := by
  rw [Int.mk, Int.subNatNat, Nat.zero_sub, Nat.sub_zero]

@[simp] theorem zero_mk (n) : (0 ⊖ n) = negOfNat n :=
  match n with
  | 0 => rfl
  | _+1 => rfl

protected def recMk.{u} {motive : Int → Sort u} (mk : (m n : Nat) → motive (m ⊖ n)) : (i : Int) → motive i
| Int.ofNat m => mk_zero m ▸ mk m 0
| Int.negSucc n => mk 0 (n + 1)

protected def recMkOn.{u} {motive : Int → Sort u} (i : Int) (mk : (m n : Nat) → motive (m ⊖ n)) : motive i := Int.recMk mk i

protected def casesMkOn.{u} {motive : Int → Sort u} (i : Int) (mk : (m n : Nat) → motive (m ⊖ n)) : motive i := Int.recMk mk i
