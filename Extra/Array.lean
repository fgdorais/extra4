/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Tactic.Cast
import Extra.Tactic.Trans

namespace Array

theorem eq_empty_of_size_eq_zero {as : Array α} (h : as.size = 0) : as = #[] := by
  apply ext
  · simp [h]
  · intros; contradiction

theorem eq_push_of_size_ne_zero [Inhabited α] {as : Array α} (h : as.size ≠ 0) : as = as.pop.push as.back := by
  apply ext
  · simp [Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero h)]
  · intros i h h'
    if hlt : i < as.pop.size then
      rw [get_push_lt (h:=hlt), getElem_pop]
    else
      have heq : i = as.pop.size := Nat.le_antisymm (size_pop .. ▸ Nat.le_pred_of_lt h) (Nat.le_of_not_gt hlt)
      cases heq; rw [get_push_eq, back, ←size_pop, get!_eq_getD, getD, dif_pos h]; rfl

/--
Custom recursor that views `Array α` as an inductive type with two constructors `Array.empty`
and `Array.push`.
-/
@[elab_as_elim]
def recPush {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) (xs) : motive xs :=
  aux xs xs.size rfl
where
  aux (xs : Array α) (n : Nat) (h : xs.size = n) : motive xs :=
    match n with
    | 0 => eq_empty_of_size_eq_zero h ▸ empty
    | n+1 =>
      have : xs.size ≠ 0 := h ▸ Nat.succ_ne_zero _
      have _ : Inhabited α := ⟨xs[0]'(Nat.zero_lt_of_ne_zero this)⟩
      eq_push_of_size_ne_zero this ▸ push xs.pop xs.back (aux xs.pop n (size_pop _ ▸ h ▸ Nat.pred_succ _))

@[simp]
theorem recPush_empty {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) :
    recPush empty push #[] = empty := rfl

theorem recPush_push {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) (xs x) :
    recPush empty push (xs.push x) = push xs x (recPush empty push xs) := by
  let _ : Inhabited α := ⟨(xs.push x)[0]⟩
  rw [recPush]
  trans (recPush.aux empty push (xs.push x) (xs.size + 1) (size_push xs x))
  · congr; exact size_push ..
  · rw [recPush.aux]; simp
    elim_cast
    congr
    · exact pop_push ..
    · exact back_push ..
    · exact pop_push ..
    · exact proof_irrel_heq ..

@[elab_as_elim, inherit_doc recPush]
def recPushOn {motive : Array α → Sort _} (xs) (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) : motive xs :=
  recPush empty push xs

@[simp]
theorem recPushOn_empty {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) :
    recPushOn #[] empty push = empty := rfl

theorem recPushOn_push {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive xs → motive (xs.push x)) (xs x) :
    recPushOn (xs.push x) empty push = push xs x (recPushOn xs empty push) := recPush_push ..

@[elab_as_elim, inherit_doc recPush]
def casesPushOn {motive : Array α → Sort _} (xs) (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive (xs.push x)) : motive xs :=
  recPush empty (fun xs x _ => push xs x) xs

@[simp]
theorem casePushOn_empty {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive (xs.push x)) :
    casesPushOn #[] empty push = empty := rfl

@[simp]
theorem casesPushOn_push {motive : Array α → Sort _} (empty : motive #[])
    (push : (xs : Array α) → (x : α) → motive (xs.push x)) (xs x) :
    casesPushOn (xs.push x) empty push = push xs x := recPush_push ..
