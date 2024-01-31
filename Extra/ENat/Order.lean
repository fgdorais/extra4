import Extra.ENat.Basic

namespace ENat

protected def le (x y : ENat) : Prop := ∀ n, x.leNat n = true ∨ y.leNat n = false
instance : LE ENat := ⟨ENat.le⟩

protected def lt (x y : ENat) : Prop := ∃ n, x.leNat n = true ∧ y.leNat n = false
instance : LT ENat := ⟨ENat.lt⟩

protected theorem not_lt {x y : ENat} : ¬ x < y ↔ y ≤ x := by
  constructor
  · intro h n
    match hx : x.leNat n, hy : y.leNat n with
    | false, _ => right; rfl
    | _, true => left; rfl
    | true, false => absurd h; exists n
  · intro h ⟨n₀, hx, hy⟩
    cases h n₀ with
    | inl h => apply Bool.false_ne_true; rw [← hy, h]
    | inr h => apply Bool.false_ne_true; rw [← hx, h]

theorem zero_le (x : ENat) : 0 ≤ x := by
  intro n; simp only [OfNat.ofNat, leNat_ofNat_iff_le]; left; exact Nat.zero_le ..

theorem le_infinity (x : ENat) : x ≤ ∞ := by
  intro n; right; rfl

theorem le_refl (x : ENat) : x ≤ x := by
  intro n; cases x.leNat n <;> trivial

theorem le_trans {x y z : ENat} : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz n
  match hx : x.leNat n, hy : y.leNat n, hz : z.leNat n with
  | true, true, true => trivial
  | true, true, false => trivial
  | true, false, true => trivial
  | true, false, false => trivial
  | false, true, true =>
    cases hxy n with
    | inl h => left; rw [← hx, ← h]
    | inr h => left; rw [← hy, ← h]
  | false, true, false => trivial
  | false, false, true =>
    cases hyz n with
    | inl h => left; rw [← hy, ← h]
    | inr h => left; rw [← hz, ← h]
  | false, false, false => trivial

theorem le_antisymm {x y : ENat} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx; ext n
  match hx : x.leNat n, hy : y.leNat n with
  | true, true => rfl
  | true, false =>
    cases hyx n with
    | inl h => rw [← hy, ← h]
    | inr h => rw [← hx, ← h]
  | false, true =>
    cases hxy n with
    | inl h => rw [← hx, ← h]
    | inr h => rw [← hy, ← h]
  | false, false => rfl

theorem le_of_eq {x y : ENat} : x = y → x ≤ y
  | rfl => le_refl _

theorem le_of_lt {x y : ENat} : x < y → x ≤ y
  | ⟨n₀, hx, hy⟩, n => by
    cases Nat.le_total n n₀ with
    | inl h => right; rw [Bool.eq_false_iff] at hy ⊢; apply mt _ hy; exact leNat_of_le_of_leNat h
    | inr h => left; exact leNat_of_le_of_leNat h hx

theorem lt_irrefl (x : ENat) : ¬ x < x := by
  rw [ENat.not_lt]; exact le_refl _

theorem lt_of_le_of_lt {x y z : ENat} : x ≤ y → y < z → x < z := by
  intro hxy ⟨n, hy, hz⟩
  cases hxy n with
  | inl hx => exists n
  | inr h => absurd Bool.false_ne_true; rw [← hy, ← h]

theorem lt_of_lt_of_le {x y z : ENat} : x < y → y ≤ z → x < z := by
  intro ⟨n, hx, hy⟩ hyz
  cases hyz n with
  | inl h => absurd Bool.false_ne_true; rw [← hy, ← h]
  | inr hz => exists n

theorem lt_trans {x y z : ENat} : x < y → y < z → x < z := by
  intro hxy hyz; exact lt_of_lt_of_le hxy (le_of_lt hyz)

theorem eq_zero_of_le_zero {x : ENat} : x ≤ 0 → x = 0 := (le_antisymm . (zero_le x))

theorem eq_infinity_of_infinity_le {x : ENat} : ∞ ≤ x → x = ∞ := le_antisymm (le_infinity x)

theorem le_coe_of_leNat_eq_true {x : ENat} {n : Nat} : x.leNat n = true → x ≤ n := by
  intro h k; cases Nat.lt_or_ge k n with
  | inl hlt =>
    right; rw [← Nat.not_le, ← leNat_ofNat_iff_le] at hlt; rw [Bool.eq_false_iff]; exact hlt
  | inr hge =>
    left; exact leNat_of_le_of_leNat hge h

theorem leNat_eq_true_of_le_coe {x : ENat} {n : Nat} : x ≤ n → x.leNat n := by
  intro h; cases h n with
  | inl h => exact h
  | inr h => absurd h; rw [Bool.not_eq_false, leNat_ofNat_iff_le]; exact Nat.le_refl ..

theorem leNat_eq_true_iff_le_coe {x : ENat} {n : Nat} : x.leNat n = true ↔ x ≤ n :=
  ⟨le_coe_of_leNat_eq_true, leNat_eq_true_of_le_coe⟩

theorem leNat_eq_false_of_coe_lt {n : Nat} {x : ENat} : n < x → x.leNat n = false := by
  intro ⟨m, h, hm⟩
  rw [leNat_ofNat_iff_le] at h
  rw [← Bool.not_eq_true] at hm ⊢
  apply mt _ hm
  exact leNat_of_le_of_leNat h

theorem coe_lt_of_leNat_eq_false {n : Nat} {x : ENat} : x.leNat n = false → n < x := by
  intro h; exists n; constructor
  · rw [leNat_ofNat_iff_le]; exact Nat.le_refl _
  · exact h

theorem leNat_eq_false_iff_coe_lt {n : Nat} {x : ENat} : x.leNat n = false ↔ n < x :=
  ⟨coe_lt_of_leNat_eq_false, leNat_eq_false_of_coe_lt⟩

theorem coe_lt_iff_coe_succ_le {n : Nat} {x : ENat} : n < x ↔ (n+1 : Nat) ≤ x := by
  constructor
  · intro ⟨m, h, hm⟩ k
    rw [leNat_ofNat_iff_le] at h ⊢
    cases Nat.lt_or_ge n k with
    | inl hlt =>
      left
      exact hlt
    | inr hge =>
      right
      rw [← Bool.not_eq_true] at hm ⊢
      apply mt _ hm
      apply leNat_of_le_of_leNat
      exact Nat.le_trans hge h
  · intro h
    refine lt_of_lt_of_le ?_ h
    exists n
    simp [ENat.ofNat, Bool.eq_false_iff]

theorem eq_ofNat_of_le_ofNat {x : ENat} {n : Nat} (h : x ≤ n) : ∃ m ≤ n, x = m := by
  induction n with
  | zero =>
    exists 0
    constructor
    · exact Nat.le_refl ..
    · exact eq_zero_of_le_zero h
  | succ n ih =>
    cases hn : x.leNat n with
    | true =>
      rw [leNat_eq_true_iff_le_coe] at hn
      match ih hn with
      | ⟨m, h, hm⟩ =>
        exists m
        constructor
        · exact Nat.le_succ_of_le h
        · exact hm
    | false =>
      rw [leNat_eq_false_iff_coe_lt] at hn
      exists n+1
      constructor
      · exact Nat.le_refl ..
      · apply le_antisymm h
        exact coe_lt_iff_coe_succ_le.1 hn

instance : Trans (α:=ENat) (β:=ENat) (γ:=ENat) (.≤.) (.≤.) (.≤.) := ⟨ENat.le_trans⟩

instance : Trans (α:=ENat) (β:=ENat) (γ:=ENat) (.<.) (.<.) (.<.) := ⟨ENat.lt_trans⟩

instance : Trans (α:=ENat) (β:=ENat) (γ:=ENat) (.≤.) (.<.) (.<.) := ⟨ENat.lt_of_le_of_lt⟩

instance : Trans (α:=ENat) (β:=ENat) (γ:=ENat) (.<.) (.≤.) (.<.) := ⟨ENat.lt_of_lt_of_le⟩
