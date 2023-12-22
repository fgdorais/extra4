import Extra.Index.Basic
import Extra.Index.Bind
import Extra.Index.Map
import Extra.Index.Pi

namespace List

protected abbrev arr {α β} (xs : List α) (ys : List β) : List (Index xs → β) :=
  xs.pi (β := fun _ => β) fun _ => ys

namespace Index
variable {α β} {xs : List α} {ys : List β}

def arr : (Index xs → Index ys) → Index (List.arr xs ys) := pi (β := fun _ => β) (f := fun _ => ys)

def unarr : Index (List.arr xs ys) → Index xs → Index ys := unpi (β := fun _ => β) (f := fun _ => ys)

theorem unarr_arr (h : Index xs → Index ys) : unarr (arr h) = h := by
  rw [arr, unarr, unpi_pi]

theorem arr_unarr (k : Index (List.arr xs ys)) : arr (unarr k) = k := by
  rw [arr, unarr, pi_unpi]

theorem arr_eq_iff_eq_unarr (h : Index xs → Index ys) (k : Index (List.arr xs ys)) : arr h = k ↔ h = unarr k := by
  constructor
  · intro h; rw [←h, unarr_arr]
  · intro h; rw [h, arr_unarr]

theorem unarr_eq_iff_eq_arr (k : Index (List.arr xs ys)) (h : Index xs → Index ys) : unarr k = h ↔ k = arr h := by
  constructor
  · intro h; rw [←h, arr_unarr]
  · intro h; rw [h, unarr_arr]

def arrEquiv (xs : List α) (ys : List β) : Equiv (Index xs → Index ys) (Index (List.arr xs ys)) where
  fwd := arr
  rev := unarr
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unarr_arr ..
    · intro | rfl => exact arr_unarr ..
