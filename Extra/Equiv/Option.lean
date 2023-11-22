/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

protected def Option.equiv {α β} (e : Equiv α β) : Equiv (Option α) (Option β) where
  fwd
  | some x => some (e.fwd x)
  | none => none
  rev
  | some x => some (e.rev x)
  | none => none
  fwd_eq_iff_rev_eq := by
    intro
    | some _, some _ =>
      constructor
      · intro | rfl => simp only [e.rev_fwd]
      · intro | rfl => simp only [e.fwd_rev]
    | some _, none => constructor <;> (intro h; cases h)
    | none, some _ => constructor <;> (intro h; cases h)
    | none, none => constructor <;> intro | rfl => rfl
