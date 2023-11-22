/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace Quotient

protected def ind₃ {motive : Quotient sa → Quotient sb → Quotient sc → Prop}
    (h : ∀ a b c, motive (Quotient.mk sa a) (Quotient.mk sb b) (Quotient.mk sc c))
    (a b c) : motive a b c := by
  induction a, b using Quotient.ind₂ with
  | _ _ _ => induction c using Quotient.ind with
    | _ _ => exact h ..

protected def ind₄ {motive : Quotient sa → Quotient sb → Quotient sc → Quotient sd → Prop}
    (h : ∀ a b c d, motive (Quotient.mk sa a) (Quotient.mk sb b) (Quotient.mk sc c)
      (Quotient.mk sd d)) (a b c d) : motive a b c d := by
  induction a, b, c using Quotient.ind₃ with
  | _ _ _ _ => induction d using Quotient.ind with
    | _ _ => exact h ..
