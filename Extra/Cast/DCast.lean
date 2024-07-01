/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Cast.Basic
import Extra.Cast.DEq

/-- Dependent type casting -/
def dcast {motive : α → Sort _} (h : a = b) (t : motive a) : motive b := Eq.ndrec t h

@[elim_cast]
theorem cast_eq_dcast (h : α = β) (t : α) : cast h t = dcast (motive:=id) h t := rfl

@[elim_cast]
theorem Eq.ndrec_eq_dcast {motive : α → Sort _} (h : a = b) (t : motive a) :
    Eq.ndrec t h = dcast h t := rfl

@[simp, elim_cast]
theorem congr_dcast {β : α → Sort _} (f : (x : α) → β x → γ) (h : x = x') (y : β x) :
    f x' (dcast h y) = f x y := congr_ndrec ..

@[simp, elim_cast]
theorem dcast_id {motive : α → Sort _} (h : a = a) (t : motive a) : dcast h t = t := by cases h; rfl

@[elim_cast]
theorem dcast_comp {motive : α → Sort _} (hab : a = b) (hbc : b = c) (t : motive a) :
    dcast hbc (dcast hab t) = dcast (Eq.trans hab hbc) t := by cases hab; rfl

@[simp, elim_cast]
theorem deq_dcast_left {motive : α → Sort _} (h : a = b) (t : motive a) (u : motive c) :
    DEq (dcast h t) u ↔ DEq t u := by cases h; rfl

@[simp, elim_cast]
theorem deq_dcast_right {motive : α → Sort _} (h : b = c) (t : motive a) (u : motive b) :
    DEq t (dcast h u) ↔ DEq t u := by cases h; rfl

@[simp, elim_cast]
theorem heq_dcast_left {motive : α → Sort _} (h : a = b) (t : motive a) (u : motive c) :
    HEq (dcast h t) u ↔ HEq t u := by cases h; rfl

@[simp, elim_cast]
theorem heq_dcast_right {motive : α → Sort _} (h : b = c) (t : motive a) (u : motive b) :
    HEq t (dcast h u) ↔ HEq t u := by cases h; rfl
