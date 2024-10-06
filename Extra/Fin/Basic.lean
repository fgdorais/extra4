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
| 0, p, h => by dsimp at h; contradiction
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
| 0, _, h => by dsimp at h; contradiction
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

def findAux? (f : Fin n → Option α) (init : Option α) : Option α :=
  foldl n (fun | none, x => f x | some y, _ => some y) init

def find? (f : Fin n → Option α) : Option α := findAux? f none

theorem findAux?_some (f : Fin n → Option α) (x : α) : findAux? f (some x) = some x := by
  rw [findAux?]
  induction n with
  | zero => rw [foldl_zero]
  | succ n ih =>
    simp [foldl_succ]
    conv => rhs; rw [← ih (f := f ∘ Fin.succ)]
    congr
    funext r i
    cases r <;> rfl

theorem findAux?_zero (f : Fin 0 → Option α) (init : Option α := none) : findAux? f init = init :=
  foldl_zero ..

theorem findAux?_succ (f : Fin (n+1) → Option α) : findAux? f none = findAux? (f ∘ Fin.succ) (f 0) := by
  simp [findAux?, foldl_succ]
  congr; funext r _; cases r <;> rfl

@[simp]
theorem find?_zero (f : Fin 0 → Option α) : find? f = none := findAux?_zero ..

theorem find?_succ (f : Fin (n+1) → Option α) :
  find? f = if (f 0).isSome then f 0 else find? (f ∘ Fin.succ) := by
  match h0 : f 0 with
  | none => simp [find?, findAux?_succ, h0]
  | some x => simp [find?, findAux?_succ, findAux?_some, h0]

theorem isNone_of_find?_isNone {f : Fin n → Option α} (h : (find? f).isNone) (i : Fin n) :
    (f i).isNone := by
  induction n with
  | zero => nomatch i
  | succ n ih =>
    rw [find?_succ] at h
    split at h
    · cases h0 : f 0 <;> simp_all
    · next h0 =>
      cases i using Fin.cases with
      | zero => rw [Bool.not_eq_true, Option.not_isSome] at h0; exact h0
      | succ i => exact ih h i

theorem exists_eq_find?_of_find?_isSome {f : Fin n → Option α} (h : (find? f).isSome) :
    ∃ i, f i = find? f := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    match h0 : f 0 with
    | some x =>
      simp [find?_succ, h0]
      exists 0
    | none =>
      simp [find?_succ, h0] at h ⊢
      match ih h with | ⟨i, _⟩ => exists i.succ

theorem find?_isNone_iff_forall_isNone {f : Fin n → Option α} :
    (find? f).isNone ↔ ∀ i, (f i).isNone := by
  match h : find? f with
  | some _ =>
    have h : (find? f).isSome := by simp [h]
    constructor
    · intros
      contradiction
    · intro hi
      match exists_eq_find?_of_find?_isSome h with
      | ⟨i, heq⟩ =>
        rw [← heq] at h
        absurd h
        rw [Bool.not_eq_true, Option.not_isSome]
        exact hi ..
  | none =>
    constructor
    · intros
      apply isNone_of_find?_isNone
      rw [h, Option.isNone_none]
    · intros
      rw [Option.isNone_none]

def bfind? (p : Fin n → Bool) : Option (Fin n) :=
  Fin.find? fun i => bif p i then some i else none

instance (n : Nat) : Find (Fin n) where
  find? := bfind?
  find?_eq_none {p x} h :=
    match hx : p x with
    | false => rfl
    | true => by
      have : (bfind? p).isNone = true := by simp [h]
      absurd isNone_of_find?_isNone this x
      simp_all
  find?_eq_some {p x} h :=
    match hx : p x with
    | true => rfl
    | false => by
      have : (bfind? p).isSome = true := by simp [h]
      simp only [bfind?] at h
      match exists_eq_find?_of_find?_isSome this with
      | ⟨i, _⟩ => cases hi : p i <;> simp_all
