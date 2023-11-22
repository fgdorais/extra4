/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Equiv.Basic

protected def List.equiv (e : Equiv α β) : Equiv (List α) (List β) where
  fwd := List.map e.fwd
  rev := List.map e.rev
  fwd_eq_iff_rev_eq := by
    intros; constructor
    · intro | rfl => rw [map_map, e.comp_rev_fwd, map_id]
    · intro | rfl => rw [map_map, e.comp_fwd_rev, map_id]
