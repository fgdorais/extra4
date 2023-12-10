import Extra.Basic
import Extra.Equiv.Basic
import Extra.Tactic.Cast

namespace List

inductive Index.{u} {α : Type u} : List α → Type u where
  | head : Index (x :: xs)
  | tail : Index xs → Index (x :: xs)
  deriving Repr

instance Index.instDecidableEq : {xs : List α} → DecidableEq (Index xs)
  | _::_, head, head => isTrue rfl
  | _::_, head, tail _ => isFalse Index.noConfusion
  | _::_, tail _, head => isFalse Index.noConfusion
  | _::_, tail i, tail j =>
    match instDecidableEq i j with
    | isTrue rfl => isTrue rfl
    | isFalse h => isFalse fun | rfl => h rfl

@[reducible] def Index.val : {xs : List α} → Index xs → α
  | x::_, head => x
  | _::_, tail i => val i

instance (x : α) (xs : List α) : Inhabited (Index (x :: xs)) := ⟨Index.head⟩

namespace Index

@[elab_as_elim, inline]
protected def recNilOn {α} {motive : Index ([] : List α) → Sort _} (i : Index ([] : List α)) :
    motive i := nomatch i

@[elab_as_elim, inline]
protected alias casesNilOn := Index.recNilOn

theorem val_head (x : α) (xs : List α) : (head : Index (x::xs)).val = x := rfl

theorem val_tail (x : α) (xs : List α) (i : Index xs) : (tail (x:=x) i).val = i.val := rfl

@[inline]
protected def compare : Index xs → Index xs → Ordering
  | head, head => .eq
  | head, tail _ => .lt
  | tail _, head => .gt
  | tail i, tail j => Index.compare i j

instance instOrd (xs : List α) : Ord (Index xs) := ⟨Index.compare⟩
instance : LE (Index xs) := leOfOrd
instance : LT (Index xs) := ltOfOrd

protected def head? : (xs : List α) → Option (Index xs)
  | [] => none
  | _::_ => some head

protected def last? : (xs : List α) → Option (Index xs)
  | [] => none
  | _::xs => match Index.last? xs with
    | some i => some (tail i)
    | none => some head

protected def next? : {xs : List α} → Index xs → Option (Index xs)
  | _::_, head => Option.map tail (Index.head? _)
  | _::_, tail i => Option.map tail (Index.next? i)

protected def pred? : {xs : List α} → Index xs → Option (Index xs)
  | _::_, head => none
  | _::_, tail i =>
    match Index.pred? i with
    | some i => some (tail i)
    | none => some head

protected def find? : {xs : List α} → (p : Index xs → Bool) → Option (Index xs)
  | [], _ => none
  | _::_, p => bif p head then some head else (Index.find? fun i => p (tail i)).map tail

theorem find_some {p : Index xs → Bool} (i : Index xs) : Index.find? p = some i → p i = true := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    intro heq
    match h : p head with
    | true =>
      simp only [Index.find?, h, cond] at heq
      rw [←Option.some.inj heq, h]
    | false =>
      simp only [Index.find?, h, cond, Option.map] at heq
      split at heq
      · next h => rw [←Option.some.inj heq, ih _ h]
      · contradiction

theorem find_none {p : Index xs → Bool} (i : Index xs) : Index.find? p = none → p i = false := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    intro heq
    simp only [Index.find?, cond, Option.map] at heq
    split at heq
    · contradiction
    · cases i
      · assumption
      · split at heq
        · contradiction
        · next h => rw [ih _ h]

def search {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : Index xs :=
  match hi : Index.find? λ i => p i with
  | some i => i
  | none => absurd h $ by
    intro ⟨j, hj⟩
    have := find_none j hi
    rw [decide_eq_true hj] at this
    contradiction

theorem search_prop {p : Index xs → Prop} [DecidablePred p] (h : ∃ i, p i) : p (search h) := by
  unfold search
  split
  next h =>
    apply of_decide_eq_true
    exact find_some _ h
  next f =>
    absurd h
    intro ⟨j, hj⟩
    have := find_none j f
    rw [decide_eq_true hj] at this
    contradiction

theorem search_eq {p q : Index xs → Prop} [ip : DecidablePred p] [iq : DecidablePred q] {hp : ∃ i, p i} {hq : ∃ j, q j}  (h : p = q) : search hp = search hq := by
  cases h
  cases Subsingleton.elim ip iq
  cases Subsingleton.elim hp hq
  rfl

theorem search_ext {p q : Index xs → Prop} [DecidablePred p] [DecidablePred q] {hp : ∃ i, p i} {hq : ∃ j, q j} : (∀ i, p i ↔ q i) → search hp = search hq := by
  intro h
  apply search_eq
  funext i
  exact propext (h i)

protected def toNat : {xs : List α} → (i : Index xs) → Nat
| _, head => 0
| _, tail i => Index.toNat i + 1

@[inline]
def toNatTR (i : Index xs) : Nat :=
  let rec loop : {xs : List _} → Index xs → Nat → Nat
  | _, .head, n => n
  | _, .tail i, n => loop i (n+1)
  loop i 0

@[csimp] theorem toNat_eq_toNatTR : @Index.toNat = @Index.toNatTR := by
  funext _ _ i
  induction i with simp_all only [Index.toNat, toNatTR, toNatTR.loop]
  | tail => rw [lem]
where
  lem {α} {xs : List α} (i : Index xs) (n : Nat) : toNatTR.loop i (n+1) = toNatTR.loop i n + 1 := by
    induction i generalizing n with
    | head => rfl
    | tail _ ih => simp [toNatTR.loop, ih]

theorem toNat_lt_length (i : Index xs) : i.toNat < xs.length := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    cases i with
    | head => exact Nat.zero_lt_succ ..
    | tail => apply Nat.succ_lt_succ (ih _)

protected abbrev toFin (i : Index xs) : Fin xs.length := ⟨i.toNat, i.toNat_lt_length⟩

def ofFinTR {xs : List α} (i : Fin xs.length) : Index xs :=
  let rec loop : {xs ys : List α} → Sum (Fin xs.length) (Index ys) → Index (List.reverseAux xs ys)
  | [], _, .inr i => i
  | _ :: _, _, .inr i => loop (ys:=_::_) (.inr (.tail i))
  | _ :: _, _, .inl ⟨0, _⟩ => loop (ys:=_::_) (.inr .head)
  | _ :: _, _, .inl ⟨i+1, hi⟩ => loop (ys:=_::_) (.inl ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
  xs.reverse_reverse ▸ loop (ys:=[]) (.inl ⟨i.val, xs.length_reverse.symm ▸ i.isLt⟩)

@[implemented_by ofFinTR]
protected def ofFin : {xs : List α} → Fin xs.length → Index xs
| _::_, ⟨0,_⟩ => head
| _::_, ⟨i+1,h⟩ => tail (Index.ofFin ⟨i, Nat.lt_of_succ_lt_succ h⟩)

theorem ofFin_toFin (i : Index xs) : Index.ofFin i.toFin = i := by
  induction xs with
  | nil => cases i
  | cons x xs ih =>
    cases i with
    | head => rfl
    | tail i =>
      apply congrArg tail
      exact ih ..

theorem toNat_ofFin {xs : List α} (i : Fin xs.length) : (Index.ofFin i).toNat = i.val := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨0,_⟩ => rfl
    | ⟨i+1,h⟩ =>
      apply congrArg Nat.succ
      rw [ih]; rfl

theorem toFin_ofFin {xs : List α} (i : Fin xs.length) : (Index.ofFin i).toFin = i := by
  apply Fin.eq_of_val_eq
  apply toNat_ofFin

def equivFin : Equiv (Index xs) (Fin xs.length) where
  fwd := Index.toFin
  rev := Index.ofFin
  fwd_eq_iff_rev_eq := by
    intros; constructor
    · intro | rfl => exact ofFin_toFin ..
    · intro | rfl => exact toFin_ofFin ..

theorem val_ofFin_eq_get (xs : List α) (i : Fin xs.length) : (Index.ofFin i).val = xs.get i := by
  induction xs with
  | nil => cases i; contradiction
  | cons x xs ih =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨i+1, _⟩ => simp [Index.ofFin, ih]
