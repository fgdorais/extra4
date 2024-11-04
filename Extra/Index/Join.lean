import Extra.Index.Basic
import Extra.Index.Append

namespace List.Index

def join : {xss : List (List α)} → (i : Index xss) × (Index i.val) → Index xss.flatten
  | _, ⟨head, j⟩ => append (.inl j)
  | _, ⟨tail i, j⟩ => append (.inr (join ⟨i, j⟩))

def unjoin : {xss : List (List α)} → Index xss.flatten → (i : Index xss) × (Index i.val)
  | _::_, k =>
    match unappend k with
    | .inl j => ⟨head, j⟩
    | .inr k => ⟨tail (unjoin k).fst, (unjoin k).snd⟩

theorem unjoin_join (i : (i : Index xss) × (Index i.val)) : unjoin (join i) = i := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, _⟩ => simp only [join, unjoin, unappend_append]
    | ⟨tail _, _⟩ => simp only [join, unjoin, unappend_append]; rw [ih]

theorem join_unjoin {xss : List (List α)} (k : Index xss.flatten) : join (unjoin k) = k := by
  induction xss with
  | nil => contradiction
  | cons xs xss ih =>
    match h : unappend k with
    | .inl j => rw [unappend_eq_iff_eq_append] at h; rw [h, unjoin, unappend_append, join]
    | .inr k => rw [unappend_eq_iff_eq_append] at h; rw [h, unjoin, unappend_append, join, ih]

theorem join_eq_iff_eq_unjoin (i : (i : Index xss) × (Index i.val)) (k : Index xss.flatten) : join i = k ↔ i = unjoin k := by
  constructor
  · intro h; rw [←h, unjoin_join]
  · intro h; rw [h, join_unjoin]

theorem unjoin_eq_iff_eq_join (k : Index xss.flatten) (i : (i : Index xss) × (Index i.val)) : unjoin k = i ↔ k = join i := by
  constructor
  · intro h; rw [←h, join_unjoin]
  · intro h; rw [h, unjoin_join]

def joinEquiv (xss : List (List α)) : Equiv ((i : Index xss) × Index i.val) (Index xss.flatten) where
  fwd := join
  rev := unjoin
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unjoin_join ..
    · intro | rfl => exact join_unjoin ..

theorem val_join (i : (i : Index xss) × Index i.val) : (join i).val = i.snd.val := by
  induction xss with
  | nil => cases i; contradiction
  | cons xs xss ih =>
    match i with
    | ⟨head, j⟩ => rw [join, val_append_inl]
    | ⟨tail i, j⟩ => rw [join, val_append_inr, ih]

theorem val_unjoin {xss : List (List α)} (k : Index xss.flatten) : (unjoin k).snd.val = k.val := by
  rw [←join_unjoin k, val_join, unjoin_join]
