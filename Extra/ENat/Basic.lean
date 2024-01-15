import Extra.Basic

class Infinity (α) where
  infinity : α
notation "∞" => Infinity.infinity

structure ENat where
  leNat : Nat → Bool
  mono_step : leNat x = true → leNat (x + 1) = true

namespace ENat

@[ext] protected theorem ext : {x y : ENat} → x.leNat = y.leNat → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected def infinity : ENat where
  leNat _ := false
  mono_step := Bool.noConfusion

instance : Infinity ENat := ⟨ENat.infinity⟩

protected def ofNat (n : Nat) : ENat where
  leNat := Nat.ble n
  mono_step h := by
    rw [Nat.ble_eq] at h ⊢
    apply Nat.le_trans h
    exact Nat.le_add_right ..

instance : Coe Nat ENat := ⟨ENat.ofNat⟩

instance : OfNat ENat n := ⟨n⟩

theorem mono_add {x : ENat} : x.leNat n = true → x.leNat (n + m) = true := by
  intro h; induction m with
  | zero => exact h
  | succ _ h => exact mono_step _ h

theorem mono {x : ENat} : n ≤ m → x.leNat n = true → x.leNat m = true := by
  intro h hx
  match Nat.le.dest h with
  | ⟨_, h⟩ => cases h; exact mono_add hx

theorem mono' {e : ENat} {x y : Nat} : x ≤ y → e.leNat y = false → e.leNat x = false := by
  intro h hy; rw [Bool.eq_false_iff] at hy ⊢; exact mt (mono h) hy

theorem leNat_coe_eq_true_iff_le {n : Nat} : ENat.leNat n m = true ↔ n ≤ m := by
  rw [ENat.ofNat, Nat.ble_eq]

theorem leNat_coe_eq_false_iff_gt {n : Nat} : ENat.leNat n m = false ↔ m < n := by
  rw [Bool.eq_false_iff, ←Nat.not_le, ←leNat_coe_eq_true_iff_le]

theorem leNat_zero_eq_true (n) : ENat.leNat 0 n = true := by
  simp only [OfNat.ofNat, leNat_coe_eq_true_iff_le, Nat.zero_le]

theorem leNat_infinity_eq_false (n) : ENat.leNat ∞ n = false := rfl
