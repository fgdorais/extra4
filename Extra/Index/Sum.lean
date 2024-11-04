import Extra.Index.Basic
import Extra.Index.Append
import Extra.Index.Map

namespace List

protected abbrev coprod {α β} (xs : List α) (ys : List β) : List (Sum α β) := xs.map .inl ++ ys.map .inr

namespace Index

def sum : Sum (Index xs) (Index ys) → Index (List.coprod xs ys)
  | .inl i => append (.inl (i.map .inl))
  | .inr j => append (.inr (j.map .inr))

def unsum (k : Index (List.coprod xs ys)) : Sum (Index xs) (Index ys) :=
  match unappend k with
  | .inl i => .inl (i.unmap .inl)
  | .inr j => .inr (j.unmap .inr)

theorem unsum_sum : (i : Sum (Index xs) (Index ys)) → unsum (sum i) = i
  | .inl _ => by simp only [unsum, sum, unappend_append, unmap_map]
  | .inr _ => by simp only [unsum, sum, unappend_append, unmap_map]

theorem sum_unsum (k : Index (List.coprod xs ys)) : sum (unsum k) = k := by
  match h : unappend k with
  | .inl i => rw [unappend_eq_iff_eq_append] at h; simp only [h, unsum, unappend_append, sum, map_unmap]
  | .inr j => rw [unappend_eq_iff_eq_append] at h; simp only [h, unsum, unappend_append, sum, map_unmap]

theorem sum_eq_iff_eq_unsum (i : Sum (Index xs) (Index ys)) (k : Index (List.coprod xs ys)) : sum i = k ↔ i = unsum k := by
  constructor
  · intro h; rw [←h, unsum_sum]
  · intro h; rw [h, sum_unsum]

theorem unsum_eq_iff_eq_sum (k : Index (List.coprod xs ys)) (i : Sum (Index xs) (Index ys)) : unsum k = i ↔ k = sum i := by
  constructor
  · intro h; rw [←h, sum_unsum]
  · intro h; rw [h, unsum_sum]

def sumEquiv (xs : List α) (ys : List β) : Equiv (Sum (Index xs) (Index ys)) (Index (List.coprod xs ys)) where
  fwd := sum
  rev := unsum
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unsum_sum ..
    · intro | rfl => exact sum_unsum ..

theorem val_sum {xs : List α} {ys : List β} (i : Sum (Index xs) (Index ys)) : (match i with | .inl i => .inl i.val | .inr j => .inr j.val) = (sum i).val := by
  match i with
  | .inl i => simp only [sum, val_append, val_map]
  | .inr j => simp only [sum, val_append, val_map]

theorem val_unsum {xs : List α} {ys : List β} (k : Index (List.coprod xs ys)) : k.val = (match k.unsum with | .inl i => .inl i.val | .inr j => .inr j.val) := by
  rw [←sum_unsum k, val_sum, unsum_sum]
