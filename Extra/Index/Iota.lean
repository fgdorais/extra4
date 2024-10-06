import Extra.Index.Basic
import Extra.Index.Append
import Extra.Index.Map

namespace List

def indexIotaTR {α} (xs : List α) : List (Index xs) :=
  let rec loop : (xs : List α) → (ys : List α) → Array (Index (ys.reverse ++ xs)) → List (Index (ys.reverse ++ xs))
  | [], ys, rs => List.append_nil ys.reverse ▸ rs.toList
  | x :: xs, ys, rs =>
    have : ys.reverse ++ (x :: xs) = (x :: ys).reverse ++ xs := by
      rw [reverse_cons, append_assoc, singleton_append]
    this ▸ loop xs (x :: ys) (this ▸ rs.push (Index.append_inr Index.head))
  loop xs [] #[]

@[implemented_by indexIotaTR] -- TODO: use csimp
def indexIota {α} : (xs : List α) → List (Index xs)
| [] => []
| _::xs => Index.head :: (indexIota xs).map Index.tail

namespace Index

def iota : {xs : List α} → Index xs → Index xs.indexIota
| _::_, Index.head => Index.head
| _::_, Index.tail i => Index.tail ((iota i).map Index.tail)

theorem val_iota (i : Index xs) : val (iota i) = i := by
  induction i with
  | head => rfl
  | tail i ih => rw [iota, val_tail, val_map, ih]

theorem iota_val {xs : List α} (i : Index xs.indexIota) : iota (val i) = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => rw [←map_unmap Index.tail i, val_tail, val_unmap Index.tail, iota, ih, map_unmap]

def iotaEquiv (xs : List α) : Equiv (Index xs) (Index xs.indexIota) where
  fwd := iota
  rev := val
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact val_iota ..
    · intro | rfl => exact iota_val ..
