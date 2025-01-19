/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.NeZero

@[ext] structure Pos where
  protected toNat : Nat
  protected ne_zero : toNat ≠ 0

namespace Pos

@[match_pattern, inline]
protected def succOfNat (n : Nat) : Pos := ⟨n.succ, Nat.noConfusion⟩

@[simp]
theorem sizeOf_succOfNat (n : Nat) : sizeOf (Pos.succOfNat n) = 1 + (n + 1) := rfl

instance (x : Pos) : NeZero x.toNat := ⟨x.ne_zero⟩

protected def ofNat? : Nat → Option Pos
  | 0 => none
  | n+1 => some (.succOfNat n)

protected def ofNat (n : Nat) [NeZero n] : Pos := ⟨n, n.ne_zero⟩

protected abbrev one : Pos := .succOfNat 0
instance : OfNat Pos (nat_lit 1) := ⟨Pos.one⟩

protected abbrev add (x y : Pos) : Pos := ⟨x.toNat + y.toNat, Nat.ne_zero _⟩
instance : Add Pos := ⟨Pos.add⟩

protected abbrev mul (x y : Pos) : Pos := ⟨x.toNat * y.toNat, Nat.ne_zero _⟩
instance : Mul Pos := ⟨Pos.mul⟩

protected abbrev pow (x : Pos) (y : Nat) : Pos := ⟨x.toNat ^ y, Nat.ne_zero _⟩
instance : Pow Pos Nat := ⟨Pos.pow⟩

protected def le (x y : Pos) : Prop := x.toNat ≤ y.toNat
instance : LE Pos := ⟨Pos.le⟩

protected def lt (x y : Pos) : Prop := x.toNat < y.toNat
instance : LT Pos := ⟨Pos.lt⟩

@[simp] theorem one_eq : Pos.one = 1 := rfl

@[simp] theorem add_eq (x y : Pos) : Pos.add x y = x + y := rfl

@[simp] theorem mul_eq (x y : Pos) : Pos.mul x y = x * y := rfl

@[simp] theorem pow_eq (x : Pos) (y : Nat) : Pos.pow x y = x ^ y := rfl

@[simp] theorem le_eq (x y : Pos) : Pos.le x y = (x ≤ y) := rfl

@[simp] theorem lt_eq (x y : Pos) : Pos.lt x y = (x < y) := rfl

instance (n : Nat) : OfNat Pos n.succ := ⟨.succOfNat n⟩

unif_hint (x : Pos) (y : Nat) where
  x =?= OfNat.ofNat y.succ ⊢ x + 1 =?= OfNat.ofNat y.succ.succ

@[elab_as_elim]
protected def recAux {motive : Pos → Sort _} (one : motive 1) (succ : (x : Pos) → motive x → motive (x+1)) : (x : Pos) → motive x
  | .succOfNat 0 => one
  | .succOfNat (n+1) => succ _ (Pos.recAux one succ (.succOfNat n))

@[elab_as_elim, induction_eliminator]
protected def recAuxOn {motive : Pos → Sort _} (x : Pos) (one : motive 1) (succ : (x : Pos) → motive x → motive (x+1)) : motive x :=
  Pos.recAux one succ x

@[elab_as_elim, cases_eliminator]
protected def casesAuxOn {motive : Pos → Sort _} (x : Pos) (one : motive 1) (succ : (x : Pos) → motive (x+1)) : motive x :=
  Pos.recAux one (fun x _ => succ x) x

@[elab_as_elim]
protected def recDiagAux.{u} {motive : Pos → Pos → Sort u}
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Pos) → motive x y :=
  Pos.recAux (motive := fun x => (y : Pos) → motive x y) right succ
where
  succ (x : Pos) (h : (y : Pos) → motive x y) (y : Pos) : motive (x+1) y :=
    Pos.casesAuxOn y (left (x+1)) (fun y => diag x y (h y))

@[elab_as_elim]
protected def recDiagAuxOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiagAux left right diag x y

@[elab_as_elim]
protected def casesDiagAuxOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (left : (x : Pos) → motive x 1)
  (right : (y : Pos) → motive 1 y)
  (diag : (x y : Pos) → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiagAux left right (fun x y _ => diag x y) x y

@[elab_as_elim]
protected def recDiag.{u} {motive : Pos → Pos → Sort u}
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive x 1 → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 y → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  (x y : Pos) → motive x y :=
  Pos.recDiagAux left right succ_succ
where
  left (x : Pos) : motive x 1 := Pos.recAuxOn (motive := fun x => motive x 1) x one_one succ_one
  right (y : Pos) : motive 1 y := Pos.recAuxOn y one_one one_succ

@[elab_as_elim]
protected def recDiagOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive x 1 → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 y → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive x y → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiag one_one succ_one one_succ succ_succ x y

@[elab_as_elim]
protected def casesDiagOn.{u} {motive : Pos → Pos → Sort u} (x y : Pos)
  (one_one : motive 1 1)
  (succ_one : (x : Pos) → motive (x + 1) 1)
  (one_succ : (y : Pos) → motive 1 (y + 1))
  (succ_succ : (x y : Pos) → motive (x + 1) (y + 1)) :
  motive x y := Pos.recDiag one_one (fun x _ => succ_one x) (fun y _ => one_succ y) (fun x y _ => succ_succ x y) x y
