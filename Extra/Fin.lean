import Extra.Basic

namespace Fin

/-! ### all/any -/

protected abbrev all {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr n (fun i v => p i && v) true

theorem forall_eq_true_of_all_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.all p = true → ∀ i, p i = true
| n+1, p, h, ⟨0, _⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact h.left
| n+1, p, h, ⟨i+1, hi⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact forall_eq_true_of_all_eq_true h.right ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem exists_eq_false_of_all_eq_false : {n : Nat} → {p : Fin n → Bool} → Fin.all p = false → ∃ i, p i = false
| 0, _, h => Bool.noConfusion h
| n+1, p, h => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_false_iff] at h
  match h with
  | .inl h => exists ⟨0, Nat.zero_lt_succ n⟩
  | .inr h => match exists_eq_false_of_all_eq_false h with
    | ⟨⟨i,hi⟩,hp⟩ => exists ⟨i+1, Nat.succ_lt_succ hi⟩

instance (p : Fin n → Prop) [DecidablePred p] : Decidable (∀ i, p i) :=
  match hall : Fin.all fun i => decide (p i) with
  | true => isTrue $ by
    intro i
    apply of_decide_eq_true
    exact forall_eq_true_of_all_eq_true hall i
  | false => isFalse $ by
    intro h
    match exists_eq_false_of_all_eq_false hall with
    | ⟨i, hi⟩ => absurd h i; exact of_decide_eq_false hi

theorem decide_forall_eq_all {n} (p : Fin n → Prop) [(i : Fin n) → Decidable (p i)] : decide (∀ i, p i) = Fin.all fun i => decide (p i) := by
  match h : Fin.all fun i => decide (p i) with
  | true =>
    have h := forall_eq_true_of_all_eq_true h
    apply decide_eq_true
    intro i
    apply of_decide_eq_true
    exact h i
  | false =>
    match exists_eq_false_of_all_eq_false h with
    | ⟨i, hi⟩ =>
      have hi := of_decide_eq_false hi
      apply decide_eq_false
      intro h
      apply hi
      exact h i

protected abbrev any {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr n (fun i v => p i || v) false

theorem exists_eq_true_of_any_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.any p = true → ∃ i, p i = true
| 0, _, h => Bool.noConfusion h
| n+1, p, h => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_true] at h
  match h with
  | .inl h => exists ⟨0, Nat.zero_lt_succ n⟩
  | .inr h => match exists_eq_true_of_any_eq_true h with
    | ⟨⟨i,hi⟩,hp⟩ => exists ⟨i+1, Nat.succ_lt_succ hi⟩

theorem forall_eq_false_of_any_eq_false : {n : Nat} → {p : Fin n → Bool} → Fin.any p = false → ∀ i, p i = false
| n+1, p, h, ⟨0, _⟩ => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_false_iff] at h
  exact h.left
| n+1, p, h, ⟨i+1, hi⟩ => by
  rw [Fin.any, Fin.foldr_succ, Bool.or_eq_false_iff] at h
  exact forall_eq_false_of_any_eq_false h.right ⟨i, Nat.lt_of_succ_lt_succ hi⟩

instance (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  match hany : Fin.any fun i => decide (p i) with
  | true => isTrue $ by
    match exists_eq_true_of_any_eq_true hany with
    | ⟨i, h⟩ => exists i; exact of_decide_eq_true h
  | false => isFalse $ by
    intro ⟨i, h⟩
    absurd h
    apply of_decide_eq_false
    exact forall_eq_false_of_any_eq_false hany i

theorem decide_exists_eq_any {n} (p : Fin n → Prop) [(i : Fin n) → Decidable (p i)] : decide (∃ i, p i) = Fin.any fun i => decide (p i) := by
  match h : Fin.any fun i => decide (p i) with
  | true =>
    match exists_eq_true_of_any_eq_true h with
    | ⟨i, hi⟩ =>
      have hi := of_decide_eq_true hi
      apply decide_eq_true
      exists i
  | false =>
    have h := forall_eq_false_of_any_eq_false h
    apply decide_eq_false
    intro ⟨i, hi⟩
    absurd hi
    apply of_decide_eq_false
    exact h i
