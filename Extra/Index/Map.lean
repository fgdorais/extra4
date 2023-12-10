import Extra.Index.Basic

namespace List.Index

@[inline]
def mapImpl (f : α → β) {xs : List α} (i : Index xs) : Index (xs.map f) :=
  Index.ofFin ⟨i.toNat, xs.length_map f ▸ i.toNat_lt_length⟩

@[implemented_by mapImpl]
def map (f : α → β) : {xs : List α} → Index xs → Index (xs.map f)
  | _, head => head
  | _, tail i => tail (map f i)

@[inline]
def unmapImpl (f : α → β) {xs : List α} (i : Index (xs.map f)) : Index xs :=
  Index.ofFin ⟨i.toNat, xs.length_map f ▸ i.toNat_lt_length⟩

@[implemented_by unmapImpl]
def unmap (f : α → β) : {xs : List α} → Index (xs.map f) → Index xs
  | _::_, head => head
  | _::_, tail i => tail (unmap f i)

theorem unmap_map (f : α → β) {xs : List α} (i : Index xs) : (i.map f).unmap f = i := by
  induction i with
  | head => rfl
  | tail i ih => exact congrArg tail ih

theorem map_unmap (f : α → β) {xs : List α} (i : Index (xs.map f)) : (i.unmap f).map f = i := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match i with
    | head => rfl
    | tail i => exact congrArg tail (ih i)

theorem map_eq_iff_eq_unmap (f : α → β) {xs : List α} (i : Index xs) (j : Index (xs.map f)) : i.map f = j ↔ i = j.unmap f := by
  constructor
  · intro h; rw [←h, unmap_map]
  · intro h; rw [h, map_unmap]

theorem unmap_eq_iff_eq_map (f : α → β) {xs : List α} (i : Index (xs.map f)) (j : Index xs) : i.unmap f = j ↔ i = j.map f := by
  constructor
  · intro h; rw [←h, map_unmap]
  · intro h; rw [h, unmap_map]

def mapEquiv (f : α → β) (xs : List α) : Equiv (Index xs) (Index (xs.map f)) where
  fwd := map f
  rev := unmap f
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unmap_map ..
    · intro | rfl => exact map_unmap ..

theorem val_map (f : α → β) {xs : List α} (i : Index xs) : (i.map f).val = f i.val := by
  induction i with
  | head => rfl
  | tail _ ih => exact ih

theorem val_unmap (f : α → β) {xs : List α} (i : Index (xs.map f)) : i.val = f (i.unmap f).val := by
  rw [←map_unmap f i, val_map, unmap_map]
