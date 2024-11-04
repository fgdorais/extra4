import Extra.Index.Basic
import Extra.Index.Bind
import Extra.Index.Map

namespace List

protected def pi {α} {β : α → Type _} (f : (x : α) → List (β x)) : (xs : List α) → List ((i : Index xs) → β i.val)
| [] => [(nomatch .)]
| x::xs => (List.pi f xs).flatMap fun ys => (f x).map fun y i => match i with | .head => y | .tail i => ys i

namespace Index
variable {α} {β : α → Type _} {f : (x : α) → List (β x)} {xs : List α}

def pi : {xs : List α} → ((i : Index xs) → Index (f i.val)) → Index (xs.pi f)
| [], _ => head
| _::_, y => bind _ ⟨pi fun i => y i.tail, map _ (y head)⟩

def unpi : {xs : List α} → (Index (xs.pi f)) → (i : Index xs) → Index (f i.val)
| _::_, k, head =>
  match unbind _ k with | ⟨_, k⟩ => unmap _ k
| _::_, k, tail i =>
  match unbind _ k with | ⟨k, _⟩ => unpi k i

theorem unpi_pi (h : (i : Index xs) → Index (f i.val)) : unpi (pi h) = h := by
  funext i
  induction i with
  | head => simp only [pi, unpi]; rw [unbind_bind, unmap_map]
  | tail i ih => simp only [pi, unpi]; rw [unbind_bind, ih]

theorem pi_unpi (k : Index (xs.pi f)) : pi (unpi k) = k := by
  induction xs with
  | nil =>
    cases k
    · rfl
    · contradiction
  | cons x xs ih =>
    match h : unbind _ k with
    | ⟨k₁,k₂⟩ =>
      rw [unbind_eq_iff_eq_bind] at h
      cases h
      simp only [pi, unpi]
      rw [unbind_bind, ih, map_unmap]

theorem pi_eq_iff_eq_unpi (h : (i : Index xs) → Index (f i.val)) (k : Index (xs.pi f)) : pi h = k ↔ h = unpi k := by
  constructor
  · intro h; rw [←h, unpi_pi]
  · intro h; rw [h, pi_unpi]

theorem unpi_eq_iff_eq_pi (k : Index (xs.pi f)) (h : (i : Index xs) → Index (f i.val)) : unpi k = h ↔ k = pi h := by
  constructor
  · intro h; rw [←h, pi_unpi]
  · intro h; rw [h, unpi_pi]

def piEquiv (xs : List α) (f : (x : α) → List (β x)) : Equiv ((i : Index xs) → Index (f i.val)) (Index (xs.pi f)) where
  fwd := pi
  rev := unpi
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unpi_pi ..
    · intro | rfl => exact pi_unpi ..
