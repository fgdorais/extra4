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
    | inl h => simp only [h] at hy
    | inr h => simp only [h] at hx

theorem zero_le (x : ENat) : 0 ≤ x := by
  intro n; simp only [OfNat.ofNat, leNat_coe_eq_true_iff_le]; left; exact Nat.zero_le ..

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
    | inl h => simp only [h] at hx
    | inr h => simp only [h] at hy
  | false, true, false => trivial
  | false, false, true =>
    cases hyz n with
    | inl h => simp only [h] at hy
    | inr h => simp only [h] at hz
  | false, false, false => trivial

theorem le_antisymm {x y : ENat} : x ≤ y → y ≤ x → x = y := by
  intro hxy hyx; ext n
  match hx : x.leNat n, hy : y.leNat n with
  | true, true => rfl
  | true, false =>
    cases hyx n with
    | inl h => simp only [h] at hy
    | inr h => simp only [h] at hx
  | false, true =>
    cases hxy n with
    | inl h => simp only [h] at hx
    | inr h => simp only [h] at hy
  | false, false => rfl

theorem le_of_eq {x y : ENat} : x = y → x ≤ y
  | rfl => le_refl _

theorem le_of_lt {x y : ENat} : x < y → x ≤ y
  | ⟨n₀, hx, hy⟩, n => by
    cases Nat.le_total n n₀ with
    | inl h => right; exact mono' h hy
    | inr h => left; exact mono h hx

theorem lt_irrefl (x : ENat) : ¬ x < x := by
  rw [ENat.not_lt]; exact le_refl _

theorem lt_of_le_of_lt {x y z : ENat} : x ≤ y → y < z → x < z := by
  intro hxy ⟨n, hy, hz⟩
  cases hxy n with
  | inl hx => exists n
  | inr h => simp only [h] at hy

theorem lt_of_lt_of_le {x y z : ENat} : x < y → y ≤ z → x < z := by
  intro ⟨n, hx, hy⟩ hyz
  cases hyz n with
  | inl h => simp only [h] at hy
  | inr hz => exists n

theorem lt_trans {x y z : ENat} : x < y → y < z → x < z := by
  intro hxy hyz; exact lt_of_lt_of_le hxy (le_of_lt hyz)

theorem eq_zero_of_le_zero {x : ENat} : x ≤ 0 → x = 0 := (le_antisymm . (zero_le x))

theorem eq_infinity_of_infinity_le {x : ENat} : ∞ ≤ x → x = ∞ := le_antisymm (le_infinity x)

theorem le_coe_of_leNat_eq_true {x : ENat} {n : Nat} : x.leNat n = true → x ≤ n := by
  intro h k; cases Nat.lt_or_ge k n with
  | inl hlt => right; rw [leNat_coe_eq_false_iff_gt]; exact hlt
  | inr hge => left; exact mono hge h

theorem leNat_eq_true_of_le_coe {x : ENat} {n : Nat} : x ≤ n → x.leNat n := by
  intro h; cases h n with
  | inl h => exact h
  | inr h => absurd h; simp only [leNat_coe_eq_false_iff_gt]; exact Nat.lt_irrefl _

theorem leNat_eq_true_iff_le_coe {x : ENat} {n : Nat} : x.leNat n = true ↔ x ≤ n :=
  ⟨le_coe_of_leNat_eq_true, leNat_eq_true_of_le_coe⟩

theorem leNat_eq_false_of_coe_lt {n : Nat} {x : ENat} : n < x → x.leNat n = false := by
  intro ⟨m, h, hm⟩
  rw [leNat_coe_eq_true_iff_le] at h
  exact mono' h hm

theorem coe_lt_of_leNat_eq_false {n : Nat} {x : ENat} : x.leNat n = false → n < x := by
  intro h; exists n; constructor
  · rw [leNat_coe_eq_true_iff_le]; exact Nat.le_refl _
  · exact h

theorem leNat_eq_false_iff_coe_lt {n : Nat} {x : ENat} : x.leNat n = false ↔ n < x :=
  ⟨coe_lt_of_leNat_eq_false, leNat_eq_false_of_coe_lt⟩

theorem coe_lt_iff_coe_succ_le {n : Nat} {x : ENat} : n < x ↔ (n+1 : Nat) ≤ x := by
  constructor
  · intro ⟨m, h, hm⟩ k
    rw [leNat_coe_eq_true_iff_le] at h ⊢
    cases Nat.lt_or_ge n k with
    | inl hlt => left; exact hlt
    | inr hge => right; apply mono' hge; apply mono' h; exact hm
  · intro h
    cases h n with
    | inl h => rw [leNat_coe_eq_true_iff_le] at h; absurd h; exact Nat.lt_irrefl n
    | inr h => exists n; rw [leNat_coe_eq_true_iff_le]; exact ⟨Nat.le_refl n, h⟩

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
