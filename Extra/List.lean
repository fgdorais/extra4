import Extra.Basic

namespace List

/-! ### extract -/

def extract (as : List α) (start stop : Nat) := (as.drop start).take (stop - start)

theorem extract_stop (as : List α) (stop : Nat) : as.extract stop stop = [] := by
  unfold extract
  rw [Nat.sub_self]
  rw [take_zero]

theorem extract_step (as : List α) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ as.length) :
  as.extract start stop = as[start]'(Nat.lt_of_lt_of_le hstart hstop) :: as.extract (start+1) stop := by
  unfold extract
  induction start, stop using Nat.recDiag generalizing as with
  | zero_zero => contradiction
  | succ_zero start => contradiction
  | zero_succ stop => match as with | a :: as => simp
  | succ_succ start stop ih =>
    match as with
    | a :: as =>
      simp
      rw [ih]
      exact Nat.lt_of_succ_lt_succ hstart
      exact Nat.le_of_succ_le_succ hstop

theorem extract_all (as : List α) : as.extract 0 as.length = as := by
  unfold extract
  rw [Nat.sub_zero]
  rw [List.drop]
  rw [take_length]

/-! ### replicate -/

theorem replicate_add {α} (a : α) : (m n : Nat) → replicate n a ++ replicate m a = replicate (m + n) a
| _, 0 => rfl
| _, _+1 => congrArg (a :: .) (replicate_add ..)

/-! ### map -/

theorem map_pure {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

theorem map_comp {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := (map_map ..).symm

/-! ### bind -/

@[simp] theorem pure_bind {α β} (f : α → List β) (a : α) : [a].flatMap f = f a := by rw [flatMap_cons, flatMap_nil, append_nil]

/-! ### repeat -/

def «repeat» (n : Nat) (l : List α) := n.fold (fun _ _ r => l ++ r) []

@[simp] theorem repeat_zero (l : List α) : l.repeat 0 = [] := rfl

theorem repeat_succ (l : List α) (n) : l.repeat (n+1) = l ++ l.repeat n := rfl
