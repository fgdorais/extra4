import Extra.Basic
import Extra.Equiv

class Find (α : Sort _) where
  find? : (α → Bool) → Option α
  find?_eq_some : find? p = some x → p x = true
  find?_eq_none : find? p = none → p x = false

namespace Find

theorem of_find?_eq_some [Find α] {p : α → Prop} [DecidablePred p] (x : α) (h : find? p = some x) : p x := by
  apply of_decide_eq_true
  apply find?_eq_some h

theorem not_of_find?_eq_none [Find α] {p : α → Prop} [DecidablePred p] (x : α) (h : find? (α:=α) p = none) : ¬ p x := by
  apply of_decide_eq_false
  apply find?_eq_none h

theorem find_is_some_iff_exists_true {α} [Find α] (p : α → Bool) : (find? p).isSome ↔ ∃ x, p x = true := by
  constructor
  · match hp : find? p with
    | some x =>
      intro
      exists x
      exact find?_eq_some hp
    | none =>
      intro
      contradiction
  · intro
    | ⟨x, hx⟩ =>
      match hp : find? p with
      | some _ =>
        rfl
      | none =>
        rw [find?_eq_none hp] at hx
        contradiction

theorem find_is_none_iff_forall_false {α} [Find α] (p : α → Bool) : (find? p).isNone ↔ ∀ x, p x = false := by
  constructor
  · match hp : find? p with
    | some x =>
      intro _
      contradiction
    | none =>
      intro _ x
      exact find?_eq_none hp
  · intro h
    match hp : find? p with
    | some x =>
      absurd find?_eq_some hp
      rw [h]
      intro
      contradiction
    | none =>
      rfl

def instInhabited [Find α] [Nonempty α] : Inhabited α where
  default :=
    match h : find? (fun _ => true) with
    | some x => x
    | none => Bool.noConfusion $ show true = false by
      cases inferInstanceAs (Nonempty α) with
      | intro x => rw [←find?_eq_none (x:=x) h]

protected def ofEquiv {α β} [Find α] (e : Equiv α β) : Find β where
  find? p :=
    match find? fun x => p (e.fwd x) with
    | some x => some (e.fwd x)
    | none => none
  find?_eq_some := by
    intro p x h
    simp at h
    split at h
    · next h' =>
      cases h
      apply find?_eq_some h'
    · contradiction
  find?_eq_none := by
    intro p x h
    simp at h
    split at h
    · contradiction
    · next h' =>
      rw [←e.fwd_rev x]
      apply find?_eq_none h'

instance [Find α] : Find (Option α) where
  find? p :=
    match p none with
    | true => some none
    | false => match find? fun x => p (some x) with
      | some x => some (some x)
      | none => none
  find?_eq_some := by intro
    | p, some x, h =>
      simp at h
      split at h
      · cases h
      · apply Find.find?_eq_some (p := fun x => p (some x))
        split at h
        · next h => cases h; assumption
        · cases h
    | p, none, h =>
      simp at h
      split at h
      · assumption
      · split at h
        · cases h
        · cases h
  find?_eq_none := by intro
    | p, some x, h =>
      simp at h
      split at h
      · cases h
      · split at h
        · cases h
        · apply find?_eq_none (p := fun x => p (some x))
          assumption
    | p, none, h =>
      simp at h
      split at h
      · cases h
      · next h =>
        split at h
        · cases h
        · assumption

instance (α β) [Find α] [Find β] : Find (Sum α β) where
  find? p :=
    match find? fun x => p (Sum.inl x), find? fun y => p (Sum.inr y) with
    | some x, _ => some (Sum.inl x)
    | _, some y => some (Sum.inr y)
    | _, _ => none
  find?_eq_some := by intro
    | p, Sum.inl x, h =>
      simp at h
      split at h
      · cases h
        apply Find.find?_eq_some (p := fun x => p (Sum.inl x))
        assumption
      · cases h
      · cases h
    | p, Sum.inr y, h =>
      simp at h
      split at h
      · cases h
      · cases h
        apply Find.find?_eq_some (p := fun y => p (Sum.inr y))
        assumption
      · next h => cases h
  find?_eq_none := by intro
    | p, Sum.inl x, h =>
      simp at h
      split at h
      · cases h
      · cases h
      · next h' _ =>
        apply Find.find?_eq_none (p := fun x => p (Sum.inl x))
        cases h: find? (fun x => p (Sum.inl x)) with
        | none => rfl
        | some x => absurd h' x; exact h
    | p, Sum.inr y, h =>
      simp at h
      split at h
      · cases h
      · cases h
      · next _ h' =>
        apply Find.find?_eq_none (p := fun x => p (Sum.inr x))
        cases h: find? (fun x => p (Sum.inr x)) with
        | none => rfl
        | some x => absurd h' x; exact h

instance (α) [Find α] (C : α → Prop) [DecidablePred C] : Find { x : α // C x } where
  find? p :=
    match find? fun x => if h: C x then p ⟨x,h⟩ else false with
    | some x => if h: C x then some ⟨x,h⟩ else none
    | none => none
  find?_eq_some := by intro
    | p, ⟨x,hx⟩ =>
      intro h
      simp at h
      split at h
      · next hsome =>
        have := find?_eq_some (p := fun x => if h: C x then p ⟨x,h⟩ else false) hsome
        split at h
        · cases h; simp [hx] at this; exact this
        · contradiction
      · contradiction
  find?_eq_none := by intro
    | p, ⟨x,hx⟩ =>
      intro h
      simp at h
      split at h
      · next hsome =>
        have := find?_eq_some (p := fun x => if h: C x then p ⟨x,h⟩ else false) hsome
        split at h
        · contradiction
        · next hx' => simp [hx'] at this
      · next hnone =>
        have := find?_eq_none (p := fun x => if h: C x then p ⟨x,h⟩ else false) (x:=x) hnone
        simp [hx] at this
        exact this

instance (α) (β : α → Type _) [Find α] [(x : α) → Find (β x)] : Find ((x : α) × β x) where
  find? p :=
    match find? fun x => Option.isSome (find? fun y => p ⟨x,y⟩) with
    | some x =>
      match find? fun y => p ⟨x,y⟩ with
      | some y => some ⟨x,y⟩
      | none => none
    | none => none
  find?_eq_some := by intro
    | p, ⟨x,y⟩ =>
      intro h
      simp at h
      split at h
      · next hsome₁ =>
        split at h
        · next hsome₂ =>
          cases h
          apply find?_eq_some (p := fun y => p ⟨x,y⟩)
          exact hsome₂
        · contradiction
      · contradiction
  find?_eq_none := by intro
    | p, ⟨x,y⟩ =>
      intro h
      simp at h
      split at h
      · next x' hsome₁ =>
        have := find?_eq_some hsome₁
        split at h
        · contradiction
        · next hnone₂ =>
          rw [hnone₂] at this
          contradiction
      · next hnone₁ =>
        have := find?_eq_none (x:=x) hnone₁
        apply find?_eq_none (p := fun y => p ⟨x,y⟩)
        cases hy: find? fun y => p ⟨x,y⟩ with
        | none => rfl
        | some _ =>
          rw [hy] at this
          contradiction

instance (α β) [Find α] [Find β] : Find (α × β) :=
  Find.ofEquiv (Sigma.equivProd α β).inv

instance (α) (r : α → α → Prop) [Find α] : Find (Quot r) where
  find? p :=
    match find? fun x => p (Quot.mk r x) with
    | some x => some (Quot.mk r x)
    | none => none
  find?_eq_some := by intro
    | p, x, h =>
      induction x using Quot.ind with
      | mk x =>
        simp at h
        split at h
        · injection h with h
          rw [←h]
          apply Find.find?_eq_some (p := fun x => p (Quot.mk r x))
          assumption
        · cases h
  find?_eq_none := by intro
    | p, x, h =>
      induction x using Quot.ind with
      | mk x =>
        simp at h
        split at h
        · cases h
        · apply Find.find?_eq_none (p := fun x => p (Quot.mk r x))
          assumption

instance (α) (s : Setoid α) [Find α] : Find (Quotient s) :=
  inferInstanceAs (Find (Quot s.r))

instance : Find Empty where
  find? _ := none
  find?_eq_none {_ x} := nomatch x
  find?_eq_some {_ x} := nomatch x

instance : Find PUnit where
  find? p := if p .unit then some .unit else none
  find?_eq_none {_ x} h := match x with | .unit => by simp at h; exact h
  find?_eq_some {_ x} h := match x with | .unit => by simp at h; exact h

instance : Find Bool where
  find? p :=
    if p false then some false else if p true then some true else none
  find?_eq_none {p x} h := by
    match x, ht : p true, hf : p false with
    | true, false, _ => assumption
    | true, true, true => simp [*] at h
    | true, true, false => simp [*] at h
    | false, _, true => simp [*] at h
    | false, _, false => assumption
  find?_eq_some {p x} h := by
    match x, ht : p true, hf : p false with
    | true, true, _ => assumption
    | true, false, _ => simp [*] at h
    | false, _, false => simp [*] at h
    | false, _, true => assumption
