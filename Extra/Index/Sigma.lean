import Extra.Index.Basic
import Extra.Index.Append
import Extra.Index.Map

namespace List.Index

def sigma : {xs : List α} → (i : Index xs) × Index (f i.val) → Index (xs.sigma f)
  | x::_, ⟨head, j⟩ => append (.inl (j.map (Sigma.mk x)))
  | _::_, ⟨tail i, j⟩ => append (.inr (sigma ⟨i, j⟩))

def unsigma : {xs : List α} → Index (xs.sigma f) → (i : Index xs) × Index (f i.val)
| x::_, k =>
  match unappend k with
  | .inl j => ⟨head, j.unmap (Sigma.mk x)⟩
  | .inr k => ⟨tail (unsigma k).fst, (unsigma k).snd⟩

theorem unsigma_sigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) : unsigma (sigma i) = i := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨head, j⟩ => simp only [sigma, unsigma, unappend_append, unmap_map]
    | ⟨tail i, j⟩ => simp only [sigma, unsigma, unappend_append]; rw [ih]

theorem sigma_unsigma {xs : List α} (k : Index (xs.sigma f)) : sigma (unsigma k) = k := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    match h : unappend k with
    | .inl j => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsigma, unappend_append, sigma, map_unmap]
    | .inr k => rw [unappend_eq_iff_eq_append] at h; cases h; rw [unsigma, unappend_append, sigma, ih]

theorem sigma_eq_iff_eq_unsigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) (k : Index (xs.sigma f)) : sigma i = k ↔ i = unsigma k := by
  constructor
  · intro h; cases h; rw [unsigma_sigma]
  · intro h; cases h; rw [sigma_unsigma]

theorem unsigma_eq_iff_eq_sigma {β : α → Type _} {f : (x : α) → List (β x)} (k : Index (xs.sigma f)) (i : (i : Index xs) × Index (f i.val)) : unsigma k = i ↔ k = sigma i := by
  constructor
  · intro h; cases h; rw [sigma_unsigma]
  · intro h; cases h; rw [unsigma_sigma]

def sigmaEquiv {β : α → Type _} (f : (x : α) → List (β x)) (xs : List α) : Equiv ((i : Index xs) × (Index (f i.val))) (Index (xs.sigma f)) where
  fwd := sigma
  rev := unsigma
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unsigma_sigma ..
    · intro | rfl => exact sigma_unsigma ..

theorem val_sigma {β : α → Type _} {f : (x : α) → List (β x)} (i : (i : Index xs) × Index (f i.val)) : (sigma i).val = ⟨i.fst.val, i.snd.val⟩ := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨head, j⟩ => rw [sigma, val_append_inl, val_map]
    | ⟨tail i, j⟩ => rw [sigma, val_append_inr, ih]

theorem val_unsigma {β : α → Type _} {f : (x : α) → List (β x)} {xs : List α} (k : Index (xs.sigma f)) : ⟨(unsigma k).fst.val, (unsigma k).snd.val⟩ = k.val := by
  rw [←sigma_unsigma k, val_sigma, unsigma_sigma]
