import Extra.Nat.Lemmas

namespace Nat

@[simp] theorem bit0_div_two (x) : (2 * x) / 2 = x := by omega

@[simp] theorem bit1_div_two (x) : (2 * x + 1) / 2 = x := by omega

@[simp] theorem bit0_mod_two (x) : (2 * x) % 2 = 0 := by omega

@[simp] theorem bit1_mod_two (x) : (2 * x + 1) % 2 = 1 := by omega

/-! ## Bitwise Recursors -/

@[elab_as_elim]
protected def recBit {motive : Nat → Sort _}
    (zero : motive 0)
    (bit0 : (x : Nat) → motive x → motive (2 * x))
    (bit1 : (x : Nat) → motive x → motive (2 * x + 1))
    (x : Nat) : motive x :=
  if h : x = 0 then h ▸ zero else
    match h2 : x % 2 with
    | 0 => Nat.div_add_mod x 2 ▸ h2 ▸ bit0 (x / 2) (Nat.recBit zero bit0 bit1 (x / 2))
    | 1 => Nat.div_add_mod x 2 ▸ h2 ▸ bit1 (x / 2) (Nat.recBit zero bit0 bit1 (x / 2))
    | _+2 => False.elim <| by omega

@[elab_as_elim]
protected def recBitOn {motive : Nat → Sort _} (x : Nat)
    (zero : motive 0)
    (bit0 : (x : Nat) → motive x → motive (2 * x))
    (bit1 : (x : Nat) → motive x → motive (2 * x + 1)) : motive x :=
  Nat.recBit zero bit0 bit1 x

@[elab_as_elim]
protected def casesBitOn {motive : Nat → Sort _} (x : Nat)
    (bit0 : (x : Nat) → motive (2 * x)) (bit1 : (x : Nat) → motive (2 * x + 1)) : motive x :=
  Nat.recBit (bit0 0) (fun x _ => bit0 x) (fun x _ => bit1 x) x

/-! ## bitwise -/

@[simp] theorem zero_bitwise (f y) : bitwise f 0 y = bif f false true then y else 0 := by
  rw [bitwise]; simp

@[simp] theorem bitwise_zero (f x) : bitwise f x 0 = bif f true false then x else 0 := by
  rw [bitwise]; split <;> simp [*]

theorem pos_bitwise_pos (f) (hx : x ≠ 0) (hy : y ≠ 0) :
  bitwise f x y = 2 * bitwise f (x / 2) (y / 2) + bif f (x % 2 = 1) (y % 2 = 1) then 1 else 0 := by
  rw [bitwise]
  simp [hx, hy]
  split <;> simp [*, Nat.two_mul]

theorem bitwise_flip (f x y) : bitwise f x y = bitwise (flip f) y x := by
  if x = 0 then
    simp [*, flip]
  else if y = 0 then
    simp [*, flip]
  else
    simp [*, pos_bitwise_pos, flip, bitwise_flip f (x / 2) (y / 2)]

theorem bit0_bitwise_bit0 (f) (hx : x ≠ 0) (hy : y ≠ 0) :
    bitwise f (2 * x) (2 * y) = 2 * bitwise f x y + bif f false false then 1 else 0 := by
  have hx2 : 2 * x ≠ 0 := by intro h; simp [Nat.mul_eq_zero] at h; contradiction
  have hy2 : 2 * y ≠ 0 := by intro h; simp [Nat.mul_eq_zero] at h; contradiction
  simp [pos_bitwise_pos _ hx2 hy2]

theorem bit1_bitwise_bit0 (f x y) :
    bitwise f (2 * x + 1) (2 * y) = 2 * bitwise f x y + bif f true false then 1 else 0 := by
  if y = 0 then
    have : 2 * y = 0 := by simp [*]
    simp [*]; cases (f true false) <;> simp [*]
  else
    have hy : 2 * y ≠ 0 := by intro h; simp [Nat.mul_eq_zero] at h; contradiction
    simp [pos_bitwise_pos _ _ hy]

theorem bit0_bitwise_bit1 (f x y) :
    bitwise f (2 * x) (2 * y + 1) = 2 * bitwise f x y + bif f false true then 1 else 0 := by
  if x = 0 then
    have : 2 * x = 0 := by simp [*]
    simp [*]; cases (f false true) <;> simp [*]
  else
    have hx : 2 * x ≠ 0 := by intro h; simp [Nat.mul_eq_zero] at h; contradiction
    simp [pos_bitwise_pos _ hx]

theorem bit1_bitwise_bit1 (f x y) :
    bitwise f (2 * x + 1) (2 * y + 1) = 2 * bitwise f x y + bif f true true then 1 else 0 := by
  simp [pos_bitwise_pos]

/-! ### Bitwise and -/

theorem and_def (x y : Nat) : (x &&& y) = bitwise (· && ·) x y := rfl

@[local simp] theorem bit0_and_bit0 (x y : Nat) : (2 * x) &&& (2 * y) = 2 * (x &&& y) := by
  if x = 0 then
    simp [*, and_def]
  else if y = 0 then
    simp [*, and_def]
  else
    simp [*, and_def, bit0_bitwise_bit0]

@[local simp] theorem bit0_and_bit1 (x y : Nat) : (2 * x) &&& (2 * y + 1) = 2 * (x &&& y) := by
  simp [and_def, bit0_bitwise_bit1]

@[local simp] theorem bit1_and_bit0 (x y : Nat) : (2 * x + 1) &&& (2 * y) = 2 * (x &&& y) :=  by
  simp [and_def, bit1_bitwise_bit0]

@[local simp] theorem bit1_and_bit1 (x y : Nat) : (2 * x + 1) &&& (2 * y + 1) = 2 * (x &&& y) + 1 := by
  simp [and_def, bit1_bitwise_bit1]

@[simp] theorem and_self (x : Nat) : x &&& x = x := by
  induction x using Nat.recBit <;> simp [*]

theorem and_comm (x y : Nat) : x &&& y = y &&& x := by
  induction x using Nat.recBit generalizing y <;> cases y using Nat.casesBitOn <;> simp [*]

theorem and_assoc (x y z : Nat) : (x &&& y) &&& z = x &&& (y &&& z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

instance : Std.Associative (α:=Nat) (· &&& ·) where
  assoc := and_assoc

instance : Std.Commutative (α:=Nat) (· &&& ·) where
  comm := and_comm

instance : Std.IdempotentOp (α:=Nat) (· &&& ·) where
  idempotent := and_self

/-! ### Bitwise or -/

theorem or_def (x y : Nat) : (x ||| y) = bitwise (· || ·) x y := rfl

@[local simp] theorem bit0_or_bit0 (x y : Nat) : (2 * x) ||| (2 * y) = 2 * (x ||| y) := by
  if x = 0 then
    simp [*, or_def]
  else if y = 0 then
    simp [*, or_def]
  else
    simp [*, or_def, bit0_bitwise_bit0]

@[local simp] theorem bit0_or_bit1 (x y : Nat) : (2 * x) ||| (2 * y + 1) = 2 * (x ||| y) + 1:= by
  simp [or_def, bit0_bitwise_bit1]

@[local simp] theorem bit1_or_bit0 (x y : Nat) : (2 * x + 1) ||| (2 * y) = 2 * (x ||| y) + 1 := by
  simp [or_def, bit1_bitwise_bit0]

@[local simp] theorem bit1_or_bit1 (x y : Nat) : (2 * x + 1) ||| (2 * y + 1) = 2 * (x ||| y) + 1 := by
  simp [or_def, bit1_bitwise_bit1]

@[simp] theorem or_self (x : Nat) : x ||| x = x := by
  induction x using Nat.recBit <;> simp [*]

theorem or_comm (x y : Nat) : x ||| y = y ||| x := by
  induction x using Nat.recBit generalizing y <;> cases y using Nat.casesBitOn <;> simp [*]

theorem or_assoc (x y z : Nat) : (x ||| y) ||| z = x ||| (y ||| z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

theorem and_or_distrib (x y z : Nat) : x &&& (y ||| z) = (x &&& y) ||| (x &&& z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

theorem or_and_distrib (x y z : Nat) : (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

instance : Std.Associative (α:=Nat) (· ||| ·) where
  assoc := or_assoc

instance : Std.Commutative (α:=Nat) (· ||| ·) where
  comm := or_comm

instance : Std.IdempotentOp (α:=Nat) (· ||| ·) where
  idempotent := or_self

instance : Std.LawfulCommIdentity (α:=Nat) (· ||| ·) 0 where
  left_id := or_zero
  right_id := zero_or

/-! ### Bitwise xor -/

theorem xor_def (x y : Nat) : (x ^^^ y) = bitwise Bool.xor x y := rfl

@[local simp] theorem bit0_xor_bit0 (x y : Nat) : (2 * x) ^^^ (2 * y) = 2 * (x ^^^ y) := by
  if x = 0 then
    simp [*, xor_def]
  else if y = 0 then
    simp [*, xor_def]
  else
    simp [*, xor_def, bit0_bitwise_bit0]

@[local simp] theorem bit0_xor_bit1 (x y : Nat) : (2 * x) ^^^ (2 * y + 1) = 2 * (x ^^^ y) + 1 :=  by
  simp [xor_def, bit0_bitwise_bit1]

@[local simp] theorem bit1_xor_bit0 (x y : Nat) : (2 * x + 1) ^^^ (2 * y) = 2 * (x ^^^ y) + 1 := by
  simp [xor_def, bit1_bitwise_bit0]

@[local simp] theorem bit1_xor_bit1 (x y : Nat) : (2 * x + 1) ^^^ (2 * y + 1) = 2 * (x ^^^ y) :=  by
  simp [xor_def, bit1_bitwise_bit1]

@[simp] theorem zero_xor (x : Nat) : 0 ^^^ x = x := by
  simp [xor_def]

@[simp] theorem xor_zero (x : Nat) : x ^^^ 0 = x := by
  simp [xor_def]

@[simp] theorem xor_self (x : Nat) : x ^^^ x = 0 := by
  induction x using Nat.recBit <;> simp [*]

theorem xor_comm (x y : Nat) : x ^^^ y = y ^^^ x := by
  induction x using Nat.recBit generalizing y <;> cases y using Nat.casesBitOn <;> simp [*]

theorem xor_assoc (x y z : Nat) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

theorem and_xor_distrib (x y z : Nat) : x &&& (y ^^^ z) = (x &&& y) ^^^ (x &&& z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

theorem xor_and_distrib (x y z : Nat) : (x ^^^ y) &&& z = (x &&& z) ^^^ (y &&& z) := by
  induction x using Nat.recBit generalizing y z <;>
    cases y using Nat.casesBitOn <;> cases z using Nat.casesBitOn <;> simp [*]

instance : Std.Associative (α:=Nat) (· ^^^ ·) where
  assoc := xor_assoc

instance : Std.Commutative (α:=Nat) (· ^^^ ·) where
  comm := xor_comm

instance : Std.LawfulCommIdentity (α:=Nat) (· ^^^ ·) 0 where
  left_id := zero_xor
  right_id := xor_zero
