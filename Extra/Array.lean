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

theorem eq_push_pop_back_of_size_ne_zero [Inhabited α] {as : Array α} (h : as.size ≠ 0) : as = as.pop.push as.back := by
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
      eq_push_pop_back_of_size_ne_zero this ▸ push xs.pop xs.back (aux xs.pop n (size_pop _ ▸ h ▸ Nat.pred_succ _))

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

/-! ### empty -/

theorem size_empty : (#[] : Array α).size = 0 := rfl

theorem empty_data : (#[] : Array α).data = [] := rfl

/-! ### append -/

theorem push_eq_append_singleton (as : Array α) (x) : as.push x = as ++ #[x] := rfl

theorem size_append (as bs : Array α) : (as ++ bs).size = as.size + bs.size := by
  simp only [size, append_data, List.length_append]

theorem get_append_left {as bs : Array α} {h : i < (as ++ bs).size} (hlt : i < as.size) :
    (as ++ bs)[i] = as[i] := by
  simp only [getElem_eq_data_get]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.get_append_left (bs:=bs.data) (h':=h')]
  apply List.get_of_eq; rw [append_data]

theorem get_append_right {as bs : Array α} {h : i < (as ++ bs).size} (hle : as.size ≤ i)
    (hlt : i - as.size < bs.size := Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) :
    (as ++ bs)[i] = bs[i - as.size] := by
  simp only [getElem_eq_data_get]
  have h' : i < (as.data ++ bs.data).length := by rwa [← data_length, append_data] at h
  conv => rhs; rw [← List.get_append_right (h':=h') (h:=Nat.not_lt_of_ge hle)]
  apply List.get_of_eq; rw [append_data]

@[simp] theorem append_nil (as : Array α) : as ++ #[] = as := by
  apply ext'; simp only [append_data, empty_data, List.append_nil]

@[simp] theorem nil_append (as : Array α) : #[] ++ as = as := by
  apply ext'; simp only [append_data, empty_data, List.nil_append]

theorem append_assoc (as bs cs : Array α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  apply ext'; simp only [append_data, List.append_assoc]
