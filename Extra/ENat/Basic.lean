import Extra.Basic

class Infinity (α) where
  infinity : α
notation "∞" => Infinity.infinity

structure ENat where
  leNat : Nat → Bool
  leNat_succ : leNat x = true → leNat (x + 1) = true

namespace ENat

@[ext] protected theorem ext : {x y : ENat} → x.leNat = y.leNat → x = y
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected def infinity : ENat where
  leNat _ := false
  leNat_succ := Bool.noConfusion

instance : Infinity ENat := ⟨ENat.infinity⟩

protected def ofNat (n : Nat) : ENat where
  leNat := Nat.ble n
  leNat_succ h := by
    rw [Nat.ble_eq] at h ⊢
    apply Nat.le_trans h
    exact Nat.le_add_right ..

instance : Coe Nat ENat := ⟨ENat.ofNat⟩

instance : OfNat ENat n := ⟨n⟩

theorem leNat_add_right {x : ENat} : x.leNat n = true → x.leNat (n + m) = true := by
  intro h; induction m with
  | zero => exact h
  | succ _ h => exact leNat_succ _ h

theorem leNat_add_left {x : ENat} : x.leNat n = true → x.leNat (m + n) = true := by
  rw [Nat.add_comm]; exact leNat_add_right

theorem leNat_of_le_of_leNat {x : ENat} : n ≤ m → x.leNat n = true → x.leNat m = true := by
  intro h hx
  match Nat.le.dest h with
  | ⟨_, h⟩ => cases h; exact leNat_add_right hx

theorem leNat_ofNat_iff_le {n : Nat} : ENat.leNat n m = true ↔ n ≤ m := by
  rw [ENat.ofNat, Nat.ble_eq]

@[simp] theorem leNat_infinity_eq_false (n : Nat) : leNat ∞ n = false := rfl

@[simp] theorem leNat_zero_eq_true (n) : ENat.leNat 0 n = true := by
  simp [OfNat.ofNat, leNat_ofNat_iff_le]
