import Extra.Basic

namespace Fin

/-- `enum n` is the array of all elements of `Fin n` in order -/
def enum (n) : Array (Fin n) := Array.ofFn id

/-- `list n` is the list of all elements of `Fin n` in order -/
def list (n) : List (Fin n) := (enum n).data

/-! ### enum/list -/

@[simp] theorem size_enum (n) : (enum n).size = n := Array.size_ofFn ..

@[simp] theorem getElem_enum (i) (h : i < (enum n).size) : (enum n)[i] = ⟨i, size_enum n ▸ h⟩ :=
  Array.getElem_ofFn ..

@[simp] theorem length_list (n) : (list n).length = n := by simp [list]

@[simp] theorem get_list (i : Fin (list n).length) : (list n).get i = i.cast (length_list n) := by
  cases i; simp only [list]; rw [←Array.getElem_eq_data_get, getElem_enum, cast_mk]

@[simp] theorem list_zero : list 0 = [] := rfl

theorem list_succ (n) : list (n+1) = 0 :: (list n).map Fin.succ := by
  apply List.ext_get; simp; intro i; cases i <;> simp

/-! ### foldl -/

theorem foldl_loop_lt (f : α → Fin n → α) (x) (h : m < n) :
    foldl.loop n f x m = foldl.loop n f (f x ⟨m, h⟩) (m+1) := by
  rw [foldl.loop, dif_pos h]

theorem foldl_loop_eq (f : α → Fin n → α) (x) : foldl.loop n f x n = x := by
  rw [foldl.loop, dif_neg (Nat.lt_irrefl _)]

theorem foldl_loop (f : α → Fin (n+1) → α) (x) (h : m < n+1) :
    foldl.loop (n+1) f x m = foldl.loop n (fun x i => f x i.succ) (f x ⟨m, h⟩) m := by
  if h' : m < n then
    rw [foldl_loop_lt _ _ h, foldl_loop_lt _ _ h', foldl_loop]; rfl
  else
    cases Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.1 h')
    rw [foldl_loop_lt, foldl_loop_eq, foldl_loop_eq]
termination_by _ => n - m

theorem foldl_zero (f : α → Fin 0 → α) (x) : foldl 0 f x = x := rfl

theorem foldl_succ (f : α → Fin (n+1) → α) (x) :
    foldl (n+1) f x = foldl n (fun x i => f x i.succ) (f x 0) := foldl_loop ..

theorem foldl_eq_foldl_list (f : α → Fin n → α) (x) : foldl n f x = (list n).foldl f x := by
  induction n using Nat.recAux generalizing x with
  | zero => rfl
  | succ n ih => rw [foldl_succ, ih, list_succ, List.foldl_cons, List.foldl_map]

/-! ### foldr -/

theorem foldr_loop_zero (f : Fin n → α → α) (x) : foldr.loop n f ⟨0, Nat.zero_le _⟩ x = x := rfl

theorem foldr_loop_succ (f : Fin n → α → α) (x) (h : m < n) :
    foldr.loop n f ⟨m+1, h⟩ x = foldr.loop n f ⟨m, Nat.le_of_lt h⟩ (f ⟨m, h⟩ x) := rfl

theorem foldr_loop (f : Fin (n+1) → α → α) (x) (h : m+1 ≤ n+1) :
    foldr.loop (n+1) f ⟨m+1, h⟩ x =
      f 0 (foldr.loop n (fun i => f i.succ) ⟨m, Nat.le_of_succ_le_succ h⟩ x) := by
  induction m using Nat.recAux generalizing x with
  | zero => simp [foldr_loop_zero, foldr_loop_succ]
  | succ m ih => rw [foldr_loop_succ, ih]; rfl

theorem foldr_succ (f : Fin (n+1) → α → α) (x) :
    foldr (n+1) f x = f 0 (foldr n (fun i => f i.succ) x) := foldr_loop ..

theorem foldr_eq_foldr_list (f : Fin n → α → α) (x) : foldr n f x = (list n).foldr f x := by
  induction n using Nat.recAux with
  | zero => rfl
  | succ n ih => rw [foldr_succ, ih, list_succ, List.foldr_cons, List.foldr_map]