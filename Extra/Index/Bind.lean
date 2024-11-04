import Extra.Index.Basic
import Extra.Index.Append

namespace List.Index

def bind (f : α → List β) : {xs : List α} → (i : Index xs) × (Index (f i.val)) → Index (xs.flatMap f)
  | _::_, ⟨head, j⟩ => append_inl j
  | _::_, ⟨tail i, j⟩ => append_inr (bind f ⟨i, j⟩)

def unbind (f : α → List β) : {xs : List α} → (k : Index (xs.flatMap f)) → (i : Index xs) × (Index (f i.val))
  | _::_, k =>
    match unappend k with
    | .inl j => ⟨head, j⟩
    | .inr k => ⟨tail (unbind f k).fst, (unbind f k).snd⟩

theorem unbind_bind (f : α → List β) {xs : List α} (i : Index xs) (j : Index (f i.val)) : unbind f (bind f ⟨i, j⟩) = ⟨i, j⟩ := by
  induction i with simp only [bind, unbind, unappend_append]
  | tail _ ih => rw [ih]

theorem bind_unbind (f : α → List β) {xs : List α} (k : Index (xs.flatMap f)) : bind f (unbind f k) = k := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rw [unbind]
    split
    next h => rw [bind, append_inl, ←h, append_unappend]
    next h => rw [bind, append_inr, ih, ←h, append_unappend]

theorem bind_eq_iff_eq_unbind (f : α → List β) (i : (i : Index xs) × Index (f i.val)) (j : Index (xs.flatMap f)) : bind f i = j ↔ i = unbind f j := by
  constructor
  · intro h; rw [←h, unbind_bind]
  · intro h; rw [h, bind_unbind]

theorem unbind_eq_iff_eq_bind (f : α → List β) (i : Index (xs.flatMap f)) (j : (i : Index xs) × Index (f i.val)) : unbind f i = j ↔ i = bind f j := by
  constructor
  · intro h; rw [←h, bind_unbind]
  · intro h; rw [h, unbind_bind]

def bindEquiv (f : α → List β) (xs : List α) : Equiv ((i : Index xs) × Index (f i.val)) (Index (xs.flatMap f)) where
  fwd := bind f
  rev := unbind f
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unbind_bind ..
    · intro | rfl => exact bind_unbind ..

theorem val_bind (f : α → List β) (i : (i : Index xs) × Index (f i.val)) : (bind f i).val = i.snd.val := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨head, j⟩ => rw [bind, val_append_inl]
    | ⟨tail i, j⟩ => rw [bind, val_append_inr, ih]

theorem val_unbind (f : α → List β)  {xs : List α} (i : Index (xs.flatMap f)) : (unbind f i).snd.val = i.val := by
  rw [←bind_unbind f i, val_bind, unbind_bind]
