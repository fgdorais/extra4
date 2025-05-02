import Extra.Basic
import Extra.Find

namespace Fin

/-! ### all/any -/

protected def all {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr n (fun i v => p i && v) true

@[simp] theorem all_zero (p : Fin 0 → Bool) : Fin.all p = true :=
  foldr_zero ..

theorem all_succ (p : Fin (n+1) → Bool) : Fin.all p = (p 0 && Fin.all (p ∘ Fin.succ)) :=
  foldr_succ ..

theorem forall_eq_true_of_all_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.all p = true → ∀ i, p i = true
| n+1, p, h, ⟨0, _⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact h.left
| n+1, p, h, ⟨i+1, hi⟩ => by
  rw [Fin.all, Fin.foldr_succ, Bool.and_eq_true] at h
  exact forall_eq_true_of_all_eq_true h.right ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem exists_eq_false_of_all_eq_false : {n : Nat} → {p : Fin n → Bool} → Fin.all p = false → ∃ i, p i = false
| 0, p, h => by simp at h
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

theorem decide_forall_eq_all {n} (p : Fin n → Prop) [DecidablePred p]  [Decidable (∀ i, p i)] : decide (∀ i, p i) = Fin.all fun i => decide (p i) := by
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

protected def any {n} (p : Fin n → Bool) : Bool :=
  Fin.foldr n (fun i v => p i || v) false

@[simp] theorem any_zero (p : Fin 0 → Bool) : Fin.any p = false :=
  foldr_zero ..

theorem any_succ (p : Fin (n+1) → Bool) : Fin.any p = (p 0 || Fin.any (p ∘ Fin.succ)) :=
  foldr_succ ..

theorem exists_eq_true_of_any_eq_true : {n : Nat} → {p : Fin n → Bool} → Fin.any p = true → ∃ i, p i = true
| 0, _, h => by simp at h
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

theorem decide_exists_eq_any {n} (p : Fin n → Prop) [DecidablePred p] [Decidable (∃ i, p i)] : decide (∃ i, p i) = Fin.any fun i => decide (p i) := by
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

def sum [Add α] [OfNat α (nat_lit 0)] (f : Fin n → α) : α :=
  foldr n (fun i s => f i + s) 0

@[simp] theorem sum_zero [Add α] [OfNat α (nat_lit 0)] (f : Fin 0 → α) : sum f = 0 :=
  foldr_zero ..

theorem sum_succ [Add α] [OfNat α (nat_lit 0)] (f : Fin (n+1) → α) : sum f = f 0 + sum (f ∘ succ) :=
  foldr_succ ..

def prod [Mul α] [OfNat α (nat_lit 1)] (f : Fin n → α) : α :=
  foldr n (fun i p => f i * p) 1

@[simp] theorem prod_zero [Mul α] [OfNat α (nat_lit 1)] (f : Fin 0 → α) : prod f = 1 :=
  foldr_zero ..

theorem prod_succ [Mul α] [OfNat α (nat_lit 1)] (f : Fin (n+1) → α) : prod f = f 0 * prod (f ∘ succ) :=
  foldr_succ ..

@[deprecated Fin.exists_of_findSome?_eq_some (since := "")]
theorem exists_eq_some_of_findSome?_eq_some {f : Fin n → Option α} (h : findSome? f = some x) :
    ∃ i, f i = some x := Fin.exists_of_findSome?_eq_some h

theorem isNone_of_findSome?_isNone {f : Fin n → Option α} (h : (findSome? f).isNone) (i : Fin n) :
    (f i).isNone := by simp_all

theorem exists_eq_findSome?_of_findSome?_isSome {f : Fin n → Option α} (h : (findSome? f).isSome) :
    ∃ i, f i = findSome? f := by
  simp only [Option.isSome] at h
  split at h
  · next heq =>
    rw [heq]
    exact exists_of_findSome?_eq_some heq
  · contradiction

theorem findSome?_isNone_iff_forall_isNone {f : Fin n → Option α} :
    (findSome? f).isNone ↔ ∀ i, (f i).isNone := by
  match h : findSome? f with
  | some _ =>
    have h : (findSome? f).isSome := by simp [h]
    constructor
    · intros
      contradiction
    · intro hi
      match exists_eq_findSome?_of_findSome?_isSome h with
      | ⟨i, heq⟩ =>
        rw [← heq] at h
        absurd h
        rw [Bool.not_eq_true, Option.isSome_eq_false_iff]
        exact hi ..
  | none =>
    constructor
    · intros
      apply isNone_of_findSome?_isNone
      rw [h, Option.isNone_none]
    · intros
      rw [Option.isNone_none]

@[deprecated find? (since := "")]
def bfind? (p : Fin n → Bool) : Option (Fin n) :=
  Fin.findSome? fun i => bif p i then some i else none

instance (n : Nat) : Find (Fin n) where
  find? := find?
  find?_eq_none {p x} h :=
    match hx : p x with
    | false => rfl
    | true => by
      rw [← hx]
      exact Fin.eq_false_of_find?_eq_none h ..
  find?_eq_some {p x} h :=
    match hx : p x with
    | true => rfl
    | false => by
      rw [← hx]
      exact Fin.eq_true_of_find?_eq_some h
