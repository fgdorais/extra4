import Extra.ENat.Basic

namespace ENat

abbrev IsFinite (x : ENat) : Prop := ∃ n, x.leNat n = true

namespace IsFinite
variable (e : ENat)

private def rel (n m : Nat) : Prop := n = m + 1 ∧ e.leNat m ≠ true

private def wf (isFinite : IsFinite e) : WellFounded (IsFinite.rel e) := by
  constructor
  intro m
  match isFinite with
  | ⟨n, hn⟩ =>
    constructor
    intro t ⟨heq, hm⟩
    cases heq
    have hlt : m + 1 ≤ n := by
      rw [Nat.succ_le, ← Nat.not_le]
      intro h
      simp [leNat_of_le_of_leNat h hn] at hm
    match Nat.le.dest hlt with
    | ⟨k, hk⟩ =>
      cases hk
      induction k generalizing m with
      | zero =>
        constructor; intro
        | _, ⟨rfl, h⟩ => simp [h] at hn
      | succ k ih =>
        constructor; intro
        | _, ⟨rfl, h⟩ =>
          apply ih _ h
          · apply leNat_of_le_of_leNat _ hn
            simp_arith
          · simp_arith

end IsFinite

private def toNatAux {e : ENat} (isFinite : IsFinite e) (x : Nat) : Nat :=
  if h : e.leNat x = true then x else toNatAux isFinite (x+1)
termination_by (IsFinite.wf e isFinite).wrap x
decreasing_by trivial

private theorem toNatAux_eq {e : ENat} (isFinite : IsFinite e) (x : Nat) :
    toNatAux isFinite x = if e.leNat x then x else toNatAux isFinite (x+1) := by
  rw [toNatAux, dite_eq_ite]

private theorem leNat_toNatAux {e : ENat} (isFinite : IsFinite e) (x : Nat) :
    e.leNat (toNatAux isFinite x) := by
  rw [toNatAux_eq]
  split
  · assumption
  · apply leNat_toNatAux
termination_by (IsFinite.wf e isFinite).wrap x
decreasing_by trivial

private theorem toNatAux_le {e : ENat} (hy : e.leNat y) {x} (hle : x ≤ y) :
    toNatAux ⟨y,hy⟩ x ≤ y := by
  rw [toNatAux_eq]
  split
  · exact hle
  · apply toNatAux_le hy
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne hle
    intro | rfl => contradiction
termination_by (IsFinite.wf e ⟨y, hy⟩).wrap x
decreasing_by trivial

def toNat (e : ENat) (isFinite : IsFinite e) : Nat := toNatAux isFinite 0

theorem leNat_toNat (e : ENat) (h : IsFinite e) : e.leNat (e.toNat h) :=
  leNat_toNatAux h 0

theorem toNat_le_of_leNat {e : ENat} {x : Nat} (h : e.leNat x) : toNat e ⟨x,h⟩ ≤ x := by
  apply toNatAux_le h
  exact Nat.zero_le x

theorem leNat_iff_toNat_le (e : ENat) (h : IsFinite e) (x : Nat) : e.leNat x ↔ e.toNat h ≤ x := by
  constructor
  · exact toNat_le_of_leNat
  · intro h; exact leNat_of_le_of_leNat h (leNat_toNat ..)

@[simp] theorem toNat_ofNat (x : Nat) :
    toNat (ENat.ofNat x) ⟨x, leNat_ofNat_iff_le.mpr (Nat.le_refl _)⟩ = x := by
  apply Nat.le_antisymm
  · simp [← leNat_iff_toNat_le, leNat_ofNat_iff_le]
  · cases x with
    | zero => exact Nat.zero_le _
    | succ x =>
      apply Nat.succ_le_of_lt
      apply Nat.not_le.1
      simp_arith [← leNat_iff_toNat_le, leNat_ofNat_iff_le]

@[simp] theorem ofNat_toNat (e : ENat) (h : IsFinite e) : ENat.ofNat (toNat e h) = e := by
  ext x; cases hx : e.leNat x with
  | true => rw [leNat_ofNat_iff_le, ← leNat_iff_toNat_le, hx]
  | false =>
    rw [←Bool.not_eq_true] at hx ⊢
    apply mt _ hx
    simp [leNat_iff_toNat_le _ h, leNat_ofNat_iff_le]

theorem eq_infinity_of_not_isFinite (e : ENat) (h : ¬IsFinite e) : e = ∞ := by
  ext n; rw [leNat_infinity_eq_false]
  match hen : e.leNat n with
  | true => absurd h; exists n
  | false => rfl
