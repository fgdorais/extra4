/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Nat.Lemmas
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

/-! ### extract -/

theorem extract_loop_zero (as bs : Array α) (start : Nat) : extract.loop as 0 start bs = bs := by
  rw [extract.loop]; split <;> rfl

theorem extract_loop_succ (as bs : Array α) (size start : Nat) (h : start < as.size) :
    extract.loop as (size+1) start bs = extract.loop as size (start+1) (bs.push as[start]) := by
  rw [extract.loop, dif_pos h]; rfl

theorem extract_loop_of_ge (as bs : Array α) (size start : Nat) (h : start ≥ as.size) :
    extract.loop as size start bs = bs := by
  rw [extract.loop, dif_neg (Nat.not_lt_of_ge h)]

theorem extract_loop_eq_aux (as bs : Array α) (size start : Nat) :
    extract.loop as size start bs = bs ++ extract.loop as size start #[] := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, extract_loop_zero, append_nil]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih (bs.push _), push_eq_append_singleton]
      rw [extract_loop_succ (h:=h), ih (#[].push _), push_eq_append_singleton, nil_append]
      rw [append_assoc]
    else
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [extract_loop_of_ge (h:=Nat.le_of_not_lt h)]
      rw [append_nil]

theorem extract_loop_eq (as bs : Array α) (size start : Nat) (h : start + size ≤ as.size) :
  extract.loop as size start bs = bs ++ as.extract start (start + size) := by
  simp [extract]; rw [extract_loop_eq_aux, Nat.min_eq_left h, Nat.add_sub_cancel_left]

theorem size_extract_loop (as bs : Array α) (size start : Nat) :
    (extract.loop as size start bs).size = bs.size + min size (as.size - start) := by
  induction size using Nat.recAux generalizing start bs with
  | zero => rw [extract_loop_zero, Nat.zero_min, Nat.add_zero]
  | succ size ih =>
    if h : start < as.size then
      rw [extract_loop_succ (h:=h), ih, size_push, Nat.add_assoc, ←Nat.add_min_add_left,
        Nat.sub_succ, Nat.one_add, Nat.one_add, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)]
    else
      have h := Nat.le_of_not_gt h
      rw [extract_loop_of_ge (h:=h), Nat.sub_eq_zero_of_le h, Nat.min_zero, Nat.add_zero]

theorem size_extract (as : Array α) (start stop : Nat) :
    (as.extract start stop).size = min stop as.size - start := by
  simp [extract]; rw [size_extract_loop, size_empty, Nat.zero_add, Nat.sub_min_sub_right,
    Nat.min_assoc, Nat.min_self]

theorem get_extract_loop_lt_aux (as bs : Array α) (size start : Nat) (hlt : i < bs.size) :
    i < (extract.loop as size start bs).size := by
  rw [size_extract_loop]
  apply Nat.lt_of_lt_of_le hlt
  exact Nat.le_add_right ..

theorem get_extract_loop_lt (as bs : Array α) (size start : Nat) (hlt : i < bs.size)
    (h := get_extract_loop_lt_aux as bs size start hlt) :
    (extract.loop as size start bs)[i] = bs[i] := by
  apply Eq.trans _ (get_append_left (bs:=extract.loop as size start #[]) hlt)
  · rw [size_append]; exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)
  · congr; rw [extract_loop_eq_aux]

theorem get_extract_loop_ge_aux (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size) : start + i - bs.size < as.size := by
  have h : i < bs.size + (as.size - start) := by
      apply Nat.lt_of_lt_of_le h
      rw [size_extract_loop]
      apply Nat.add_le_add_left
      exact Nat.min_le_right ..
  rw [Nat.add_sub_assoc hge]
  apply Nat.add_lt_of_lt_sub'
  exact Nat.sub_lt_left_of_lt_add hge h

theorem get_extract_loop_ge (as bs : Array α) (size start : Nat) (hge : i ≥ bs.size)
    (h : i < (extract.loop as size start bs).size)
    (h' := get_extract_loop_ge_aux as bs size start hge h) :
    (extract.loop as size start bs)[i] = as[start + i - bs.size] := by
  induction size using Nat.recAux generalizing start bs with
  | zero =>
    rw [size_extract_loop, Nat.zero_min, Nat.add_zero] at h
    absurd h; exact Nat.not_lt_of_ge hge
  | succ size ih =>
    have : start < as.size := by
      apply Nat.lt_of_le_of_lt (Nat.le_add_right start (i - bs.size))
      rwa [← Nat.add_sub_assoc hge]
    have : i < (extract.loop as size (start+1) (bs.push as[start])).size := by
      rwa [← extract_loop_succ]
    have heq : (extract.loop as (size+1) start bs)[i] =
        (extract.loop as size (start+1) (bs.push as[start]))[i] := by
      congr 1; rw [extract_loop_succ]
    rw [heq]
    if hi : bs.size = i then
      cases hi
      have h₁ : bs.size < (bs.push as[start]).size := by rw [size_push]; exact Nat.lt_succ_self ..
      have h₂ : bs.size < (extract.loop as size (start+1) (bs.push as[start])).size := by
        rw [size_extract_loop]; apply Nat.lt_of_lt_of_le h₁; exact Nat.le_add_right ..
      have h : (extract.loop as size (start + 1) (push bs as[start]))[bs.size] = as[start] := by
        rw [get_extract_loop_lt as (bs.push as[start]) size (start+1) h₁ h₂, get_push_eq]
      rw [h]; congr; rw [Nat.add_sub_cancel]
    else
      have hge : bs.size + 1 ≤ i := Nat.lt_of_le_of_ne hge hi
      rw [ih (bs.push as[start]) (start+1) ((size_push ..).symm ▸ hge)]
      congr 1; rw [size_push, Nat.add_right_comm, Nat.add_sub_add_right]

theorem get_extract {as : Array α} {start stop : Nat} (h : i < (as.extract start stop).size)
    (h' : start + i < as.size := Nat.add_lt_of_lt_sub' (Nat.lt_of_lt_of_le (size_extract .. ▸ h)
      (Nat.sub_le_sub_right (Nat.min_le_right ..) _))) :
    (as.extract start stop)[i] = as[start + i] :=
  show (extract.loop as (min stop as.size - start) start #[])[i] = as[start + i] by
  rw [get_extract_loop_ge]; rfl; exact Nat.zero_le _

@[simp] theorem extract_all (as : Array α) : as.extract 0 as.size = as := by
  apply ext
  · rw [size_extract, Nat.min_self, Nat.sub_zero]
  · intros; rw [get_extract]; congr; rw [Nat.zero_add]

theorem extract_empty_of_stop_le_start (as : Array α) {start stop : Nat} (h : stop ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.zero_min,
    extract_loop_zero]

theorem extract_empty_of_size_le_start (as : Array α) {start stop : Nat} (h : as.size ≤ start) :
    as.extract start stop = #[] := by
  simp [extract]; rw [←Nat.sub_min_sub_right, Nat.sub_eq_zero_of_le h, Nat.min_zero,
    extract_loop_zero]

@[simp] theorem extract_empty (start stop : Nat) : (#[] : Array α).extract start stop = #[] :=
  extract_empty_of_size_le_start _ (Nat.zero_le _)
