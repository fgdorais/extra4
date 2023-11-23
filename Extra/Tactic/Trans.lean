/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

class TransDefault (r : α → α → Sort _) where
  trans : r x y → r y z → r x z

@[default_instance] instance [TransDefault r] : Trans r r r where
  trans := TransDefault.trans

syntax "trans " term:max ("using " term:max (", " term:max)?)? : tactic
macro_rules
  | `(tactic| trans $b) => `(tactic| apply Trans.trans (b:=$b))
  | `(tactic| trans $b using $r) => `(tactic| apply Trans.trans (r:=$r) (s:=$r) (b:=$b))
  | `(tactic| trans $b using $r, $s) => `(tactic| apply Trans.trans (r:=$r) (s:=$s) (b:=$b))

instance (α) : TransDefault (@Eq α) where trans := Eq.trans
instance (α) [inst : Setoid α] : TransDefault inst.r where trans := Setoid.trans
instance : TransDefault (@LE.le Nat _) where trans := Nat.le_trans
instance : TransDefault (@LT.lt Nat _) where trans := Nat.lt_trans
instance : TransDefault (@LE.le Int _) where trans := Int.le_trans
instance : TransDefault (@LT.lt Int _) where trans := Int.lt_trans
