/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

instance (β : α → Sort _) [DecidableEq α] [(i : α) → DecidableEq (β i)] : DecidableEq ((i : α) × β i)
  | ⟨i,x⟩, ⟨j,y⟩ =>
    if h : i = j then
      if h' : x = (h ▸ y) then
        isTrue (by cases h; cases h'; rfl)
      else
        isFalse fun | rfl => by contradiction
    else
      isFalse fun | rfl => by contradiction
