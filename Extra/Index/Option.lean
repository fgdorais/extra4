import Extra.Index.Basic
import Extra.Index.Map

namespace List

protected abbrev option {α} (xs : List α) : List (Option α) := none :: xs.map some

namespace Index

def option : Option (Index xs) → Index xs.option
  | none => head
  | some i => tail (i.map some)

def unoption (k : Index xs.option) : Option (Index xs) :=
  match k with
  | head => none
  | tail i => i.unmap some

theorem unoption_option : (i : Option (Index xs)) → unoption (option i) = i
  | none => rfl
  | some i => congrArg some (unmap_map some i)

theorem option_unoption : (k : Index (List.option xs)) → option (unoption k) = k
  | head => rfl
  | tail k => congrArg tail (map_unmap some k)

theorem option_eq_iff_eq_unoption (i : Option (Index xs)) (k : Index (List.option xs)) : option i = k ↔ i = unoption k := by
  constructor
  · intro h; rw [←h, unoption_option]
  · intro h; rw [h, option_unoption]

theorem unoption_eq_iff_eq_option (k : Index (List.option xs)) (i : Option (Index xs)) : unoption k = i ↔ k = option i := by
  constructor
  · intro h; rw [←h, option_unoption]
  · intro h; rw [h, unoption_option]

def optionEquiv (xs : List α) : Equiv (Option (Index xs)) (Index (List.option xs)) where
  fwd := option
  rev := unoption
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unoption_option ..
    · intro | rfl => exact option_unoption ..

theorem val_option {xs : List α} (i : Option (Index xs)) : (match i with | none => none | some i => some i.val) = (option i).val := by
  match i with
  | none => rfl
  | some i => rw [option, val_map]

theorem val_unoption {xs : List α} (k : Index (List.option xs)) : k.val = (match k.unoption with | none => none | some k => some k.val) := by
  rw [←option_unoption k, val_option, unoption_option]
