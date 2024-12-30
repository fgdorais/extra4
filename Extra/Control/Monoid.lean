import Extra.Basic

namespace Control

class Monoid (α) where
  protected op : α → α → α
  protected id : α
  fold : List α → α := List.foldr op id

export Monoid (fold)

local infixl:60 " ⋆ " => Monoid.op
local notation "e" => Monoid.id

class LawfulMonoid (α) [Monoid α] : Prop where
  id_op (x : α) : e ⋆ x = x
  op_id (x : α) : x ⋆ e = x
  op_assoc (x y z : α) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
  fold_nil : fold (α := α) [] = e := by
    intros; apply List.foldl_nil (f := Monoid.op)
  fold_cons (x : α) (xs : List α) : fold (x :: xs) = x ⋆ fold xs := by
    intros; apply List.foldr_cons (f := Monoid.op)

export LawfulMonoid (id_op op_id op_assoc fold_nil fold_cons)

attribute [simp] op_id id_op fold_nil

section LawfulMonoid
variable [Monoid α] [LawfulMonoid α]

@[simp] theorem fold_singleton (x : α) : fold [x] = x := by simp [fold_cons]

@[simp] theorem fold_pair (x y : α) : fold [x, y] = x ⋆ y := by simp [fold_cons]

theorem fold_append (xs ys : List α) : fold (xs ++ ys) = fold xs ⋆ fold ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [fold_cons, ih, op_assoc]

end LawfulMonoid

/-! ### Basic Instances -/

instance (α) : Monoid (List α) where
  id := []
  op := (· ++ ·)
  fold := List.flatten

instance (α) : LawfulMonoid (List α) where
  id_op := List.nil_append
  op_id := List.append_nil
  op_assoc := List.append_assoc
  fold_nil := List.flatten_nil
  fold_cons _ _ := List.flatten_cons

instance (α) : Monoid (Option α) where
  id := none
  op := (· <|> ·)

instance (α) : LawfulMonoid (Option α) where
  id_op := Option.none_orElse
  op_id := Option.orElse_none
  op_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl

instance (α) : Monoid (α → α) where
  id := id
  op := (· ∘ ·)

instance (α) : LawfulMonoid (α → α) where
  id_op _ := rfl
  op_id _ := rfl
  op_assoc _ _ _ := rfl

/-! ### Monoid Reflection -/

namespace Monoid
variable [Monoid α]

class Reflect (x : α) where
  list : List α
  fold_eq [LawfulMonoid α] : fold list = x

theorem eq_of_fold_eq_fold {x y : α} [Reflect x] [Reflect y] [LawfulMonoid α] :
    fold (Reflect.list x) = fold (Reflect.list y) → x = y := by
  rw [Reflect.fold_eq, Reflect.fold_eq]; exact id

theorem eq_of_list_eq_list {x y : α} [Reflect x] [Reflect y] [LawfulMonoid α] :
    Reflect.list x = Reflect.list y → x = y := by
  intro h; apply eq_of_fold_eq_fold; rw [h]

instance (priority := low) (x : α) : Reflect x where
  list := [x]
  fold_eq := fold_singleton ..

instance (xs : List α) : Reflect (no_index (fold xs)) where
  list := xs
  fold_eq := rfl

instance : Reflect (α := α) (no_index e) where
  list := []
  fold_eq := fold_nil ..

instance (x y : α) [Reflect x] [Reflect y] : Reflect (no_index (x ⋆ y)) where
  list := Reflect.list x ++ Reflect.list y
  fold_eq := by intros; rw [fold_append, Reflect.fold_eq, Reflect.fold_eq]

instance (x : α) (xs : List α) [Reflect xs] : Reflect (x :: xs) where
  list := [x] :: Reflect.list xs
  fold_eq := by intros; rw [fold_cons, Reflect.fold_eq]; rfl

end Monoid
