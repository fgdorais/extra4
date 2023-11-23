/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

syntax "trans " term:max ("using " term:max (", " term:max)?)? : tactic
macro_rules
  | `(tactic| trans $b) => `(tactic| apply Trans.trans (b:=$b))
  | `(tactic| trans $b using $r) => `(tactic| apply Trans.trans (r:=$r) (s:=$r) (b:=$b))
  | `(tactic| trans $b using $r, $s) => `(tactic| apply .trans (r:=$r) (s:=$s) (b:=$b))
