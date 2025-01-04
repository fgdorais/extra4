import Extra.Cast.DCast
import Extra.Equiv.Basic
import Extra.Fin.Basic

namespace Fin

def equivEmpty : Equiv (Fin 0) Empty where
  fwd k := nomatch k
  rev k := nomatch k
  fwd_eq_iff_rev_eq {k} := nomatch k

def equivPUnit : Equiv (Fin 1) PUnit where
  fwd _ := .unit
  rev _ := ⟨0, Nat.zero_lt_one⟩
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨0, _⟩, .unit => ⟨fun _ => rfl, fun _ => rfl⟩

abbrev equivUnit : Equiv (Fin 1) Unit := equivPUnit

def equivBool : Equiv (Fin 2) Bool where
  fwd
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  rev
  | false => ⟨0, Nat.zero_lt_succ 1⟩
  | true => ⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨0, _⟩, false  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨0, _⟩, true  => ⟨Bool.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, false  => ⟨Bool.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, true  => ⟨fun _ => rfl, fun _ => rfl⟩

def equivOrdering : Equiv (Fin 3) Ordering where
  fwd
  | ⟨0, _⟩ => .eq
  | ⟨1, _⟩ => .lt
  | ⟨2, _⟩ => .gt
  rev
  | .eq => ⟨0, Nat.zero_lt_succ 2⟩
  | .lt => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
  | .gt => ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ Nat.zero_lt_one)⟩
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨0, _⟩, .eq  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨0, _⟩, .lt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨0, _⟩, .gt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, .eq  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨1, _⟩, .lt  => ⟨fun _ => rfl, fun _ => rfl⟩
  | ⟨1, _⟩, .gt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Nat.succ.inj (Fin.val_eq_of_eq h))⟩
  | ⟨2, _⟩, .eq  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Fin.val_eq_of_eq h)⟩
  | ⟨2, _⟩, .lt  => ⟨Ordering.noConfusion, fun h => Nat.noConfusion (Nat.succ.inj (Fin.val_eq_of_eq h))⟩
  | ⟨2, _⟩, .gt  => ⟨fun _ => rfl, fun _ => rfl⟩

def encodeOptionNone : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩

def encodeOption : Option (Fin n) → Fin (n+1)
  | some i => Fin.castSucc i
  | none => Fin.last n

def decodeOption : Fin (n+1) → Option (Fin n)
  | ⟨k, _⟩ => if hk : k < n then some ⟨k, hk⟩ else none

def equivOption (n : Nat) : Equiv (Fin (n+1)) (Option (Fin n)) where
  fwd := decodeOption
  rev := encodeOption
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨k, hk⟩, some ⟨i, hi⟩ => by
    constructor
    · intro h
      simp [encodeOption, decodeOption] at h ⊢
      exact h.2.symm
    · intro h
      simp [encodeOption, decodeOption] at h ⊢
      cases h
      constructor
      · exact hi
      · rfl
  | ⟨k, hk⟩, none => by
    constructor
    · intro h
      ext
      simp [encodeOption, decodeOption] at h ⊢
      apply Nat.le_antisymm
      · exact h
      · exact Nat.le_of_lt_succ hk
    · intro h
      simp [encodeOption, decodeOption] at h ⊢
      cases h
      exact Nat.le_refl n

def encodeSumLeft : Fin m → Fin (m + n)
| ⟨i, hi⟩ => ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_add_right m n)⟩

def encodeSumRight : Fin n → Fin (m + n)
| ⟨j, hj⟩ => ⟨m + j, Nat.add_lt_add_left hj m⟩

def decodeSum : Fin (m + n) → Sum (Fin m) (Fin n)
| ⟨k, hk⟩ =>
  if hkm : k < m then
    Sum.inl ⟨k, hkm⟩
  else
    have hkm : k - m < n := by omega
    Sum.inr ⟨k - m, hkm⟩

def equivSum (m n : Nat) : Equiv (Fin (m + n)) (Sum (Fin m) (Fin n)) where
  fwd := decodeSum
  rev
  | .inl x => encodeSumLeft x
  | .inr y => encodeSumRight y
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨k, hk⟩, .inl ⟨i, hi⟩ => by
    constructor
    · intro h
      simp only [encodeSumLeft, decodeSum] at h ⊢
      split at h
      · cases h; rfl
      · contradiction
    · intro h
      simp only [encodeSumLeft, decodeSum] at h ⊢
      cases h
      split
      · rfl
      · contradiction
  | ⟨k, hk⟩, .inr ⟨j, hj⟩ => by
    constructor
    · intro h
      simp only [encodeSumRight, decodeSum] at h ⊢
      split at h
      · contradiction
      · next hkm =>
        cases h
        ext; simp only [Fin.val_mk]
        rw [Nat.add_sub_cancel']
        exact Nat.le_of_not_gt hkm
    · intro h
      simp [encodeSumRight, decodeSum] at h ⊢
      cases h
      split
      next h =>
        absurd h
        apply Nat.not_lt_of_ge
        exact Nat.le_add_right ..
      next =>
        congr
        exact Nat.add_sub_cancel_left ..

def encodeProd : Fin m × Fin n → Fin (m * n)
| (⟨i, hi⟩, ⟨j,hj⟩) => Fin.mk (n * i + j) $ calc
  _ < n * i + n := Nat.add_lt_add_left hj ..
  _ = n * (i + 1) := Nat.mul_succ ..
  _ ≤ n * m := Nat.mul_le_mul_left n (Nat.succ_le_of_lt hi)
  _ = m * n := Nat.mul_comm ..

def decodeProdLeft : Fin (m * n) → Fin m
| ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.zero_lt_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at hk
    contradiction
  Fin.mk (k / n) $ by rw [Nat.div_lt_iff_lt_mul hn]; exact hk

def decodeProdRight : Fin (m * n) → Fin n
| ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.zero_lt_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at hk
    contradiction
  ⟨k % n, Nat.mod_lt k hn⟩

abbrev decodeProd (k : Fin (m * n)) := (decodeProdLeft k, decodeProdRight k)

def equivProd (m n : Nat) : Equiv (Fin (m * n)) (Fin m × Fin n) where
  fwd := decodeProd
  rev := encodeProd
  fwd_eq_iff_rev_eq {k x} := match k, x with
  | ⟨k, hk⟩, (⟨i,hi⟩, ⟨j,hj⟩) => by
    constructor
    · intro h
      unfold decodeProd decodeProdLeft decodeProdRight at h
      unfold encodeProd
      simp at h ⊢
      cases h with
      | intro hl hr =>
        cases hl
        cases hr
        exact Nat.div_add_mod ..
    · intro h
      unfold decodeProd decodeProdLeft decodeProdRight
      unfold encodeProd at h
      simp at h ⊢
      cases h
      have hn : n > 0 := by
        apply Nat.zero_lt_of_ne_zero
        intro hz
        rw [hz, Nat.mul_zero] at hk
        contradiction
      constructor
      · rw [Nat.add_comm]
        rw [Nat.add_mul_div_left _ _ hn]
        rw [Nat.div_eq_of_lt hj]
        rw [Nat.zero_add]
      · rw [Nat.add_comm]
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt hj]

def encodeFun : {m : Nat} → (Fin m → Fin n) → Fin (n ^ m)
| 0, _ => Fin.mk 0 $ by rw [Nat.pow_zero n]; exact Nat.zero_lt_one
| m+1, f => Fin.mk (n * (encodeFun fun k => f k.succ).val + (f 0).val) $ calc
  _ < n * (encodeFun fun k => f k.succ).val + n := Nat.add_lt_add_left (f 0).isLt _
  _ = n * ((encodeFun fun k => f k.succ).val + 1) := Nat.mul_succ ..
  _ ≤ n * n ^ m := Nat.mul_le_mul_left n (Nat.succ_le_of_lt (encodeFun fun k => f k.succ).isLt)
  _ = n ^ m * n := Nat.mul_comm ..
  _ = n ^ (m+1) := Nat.pow_succ ..

def decodeFun : {m : Nat} → Fin (n ^ m) → Fin m → Fin n
| 0, _ => (nomatch .)
| m+1, ⟨k, hk⟩ =>
  have hn : n > 0 := by
    apply Nat.zero_lt_of_ne_zero
    intro h
    rw [h, Nat.pow_succ, Nat.mul_zero] at hk
    contradiction
  fun
  | ⟨0, _⟩ => ⟨k % n, Nat.mod_lt k hn⟩
  | ⟨i+1, hi⟩ =>
    have h : k / n < n ^ m := by rw [Nat.div_lt_iff_lt_mul hn]; exact hk
    decodeFun ⟨k / n, h⟩ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem specFun (k : Fin (n ^ m)) (x : Fin m → Fin n) :
  decodeFun k = x ↔ encodeFun x = k := by
  induction m with
  | zero =>
    match k with
    | ⟨0, _⟩ =>
      constructor
      · intro | rfl => rfl
      · intro; funext ⟨_,_⟩; contradiction
  | succ m ih =>
    have ih1 : decodeFun (encodeFun (fun k => x (succ k))) = fun k => x (succ k) := by rw [ih]
    match k with
    | ⟨k, hk⟩ =>
      have hnpos : n > 0 := by
        apply Nat.zero_lt_of_ne_zero
        intro h
        rw [h] at hk
        contradiction
      constructor
      · intro h
        unfold encodeFun
        ext
        simp
        apply Eq.trans (b := n * (k / n) + k % n)
        · congr
          · have : k / n < n ^ m := by rw [Nat.div_lt_iff_lt_mul hnpos]; exact hk
            have : (encodeFun fun k => x (succ k)) = ⟨k / n, this⟩ := by rw [←ih, ←h]; rfl
            simp [this]
          · rw [←h]
            unfold decodeFun
            simp only
            split
            next => rfl
            next heq => injection heq; contradiction
        · rw [Nat.add_comm]
          exact Nat.mod_add_div ..
      · intro h
        unfold encodeFun at h
        injection h with h
        unfold decodeFun
        funext ⟨i, hi⟩
        simp only
        split
        next heq =>
          cases heq
          ext
          simp only [←h]
          rw [Nat.add_comm]
          rw [Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt (x 0).isLt]
          rfl
        next i _ heq =>
          cases heq
          rw [Nat.add_comm] at h
          have : (encodeFun fun k => x (succ k)) = k / n := by
            rw [←h]
            rw [Nat.add_mul_div_left (H := hnpos)]
            rw [Nat.div_eq_of_lt (x 0).isLt]
            rw [Nat.zero_add]
          apply Eq.trans (b := (decodeFun (encodeFun fun k => x (succ k))) ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
          · congr
            rw [←h]
            rw [Nat.add_mul_div_left (H := hnpos)]
            rw [Nat.div_eq_of_lt (x 0).isLt]
            rw [Nat.zero_add]
          · rw [ih1]
            rfl

def equivFun (n m : Nat) : Equiv (Fin (n ^ m)) (Fin m → Fin n) where
  fwd := decodeFun
  rev := encodeFun
  fwd_eq_iff_rev_eq {k x} := specFun k x

def encodeSigma (f : Fin n → Nat) (x : (i : Fin n) × Fin (f i)) : Fin (sum f) :=
  match n, f, x with
  | _+1, _, ⟨⟨0, _⟩, ⟨j, hj⟩⟩ =>
    ⟨j, Nat.lt_of_lt_of_le hj (sum_succ .. ▸ Nat.le_add_right ..)⟩
  | _+1, f, ⟨⟨i+1, hi⟩, ⟨j, hj⟩⟩ =>
    match encodeSigma ((f ∘ succ)) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩ with
    | ⟨k, hk⟩ => ⟨f 0 + k, sum_succ .. ▸ Nat.add_lt_add_left hk ..⟩

def decodeSigma (f : Fin n → Nat) (k : Fin (sum f)) : (i : Fin n) × Fin (f i) :=
  match n, f, k with
  | 0, _, ⟨_, h⟩ => False.elim (by simp only [sum, foldr_zero] at h; contradiction)
  | n+1, f, ⟨k, hk⟩ =>
    if hk0 : k < f 0 then
      ⟨0, ⟨k, hk0⟩⟩
    else
      have hkf : k - f 0 < sum (f ∘ succ) := by
        apply Nat.sub_lt_left_of_lt_add
        · exact Nat.le_of_not_gt hk0
        · rw [← sum_succ]; exact hk
      match decodeSigma ((f ∘ succ)) ⟨k - f 0, hkf⟩ with
      | ⟨⟨i, hi⟩, j⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, j⟩

theorem specSigma (f : Fin n → Nat) (k : Fin (sum f)) (x : (i : Fin n) × Fin (f i)) : decodeSigma f k = x ↔ encodeSigma f x = k := by
  induction n with
  | zero => match k, x with | ⟨_, h⟩, _ => simp only [sum, foldr_zero] at h; contradiction
  | succ n ih =>
    match k, x with
    | ⟨k, hk⟩, ⟨⟨0, _⟩, ⟨_,_⟩⟩ =>
      constructor
      · intro h
        unfold decodeSigma at h
        congr
        split at h
        next => cases h; rfl
        next => cases h
      · intro h
        unfold decodeSigma
        cases h
        split
        next => rfl
        next => contradiction
    | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, ⟨j, hj⟩⟩ =>
      constructor
      · intro h
        simp only [decodeSigma] at h
        split at h
        next => cases h
        next hk0 =>
          have hk' : k - f 0 < sum (f ∘ succ) := by
            apply Nat.sub_lt_left_of_lt_add
            · exact Nat.le_of_not_gt hk0
            · rw [← sum_succ]; exact hk
          have : encodeSigma (f ∘ succ) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩ = ⟨k - f 0, hk'⟩ := by
            rw [←ih]
            injection h with h1 h2
            cases h1
            ext
            · rfl
            · exact h2
          simp [encodeSigma]
          apply Eq.trans (b := f 0 + (encodeSigma (f ∘ succ) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j, hj⟩⟩).val)
          · rfl
          · rw [this]
            rw [Nat.add_comm, Nat.sub_add_cancel]
            exact Nat.le_of_not_gt hk0
      · intro h
        simp only [decodeSigma]
        simp only [encodeSigma] at h
        split
        next hlt =>
          cases h
          absurd hlt
          apply Nat.not_lt_of_ge
          exact Nat.le_add_right ..
        next hk0 =>
          have hk' : k - f 0 < sum (f ∘ succ) := by
            apply Nat.sub_lt_left_of_lt_add
            · exact Nat.le_of_not_gt hk0
            · rw [← sum_succ]; exact hk
          have : decodeSigma (f ∘ succ) ⟨k - f 0, hk'⟩ = ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, ⟨j,hj⟩⟩ := by
            rw [ih]
            cases h
            ext
            simp only
            rw [Nat.add_sub_cancel_left]
          congr 1
          · ext
            apply Eq.trans (b := (decodeSigma (f ∘ succ) ⟨k - f 0, hk'⟩).1.1+1)
            · rfl
            · rw [this]
          · have t' : (decodeSigma (f ∘ succ) ⟨k - f 0, hk'⟩).fst.val = i := by
              rw [this]
            cases t'
            apply heq_of_eq
            apply Eq.trans (b := (decodeSigma (f ∘ succ) ⟨k - f 0, hk'⟩).2)
            · ext; rfl
            · ext; simp; rw [this]

def equivSigma (f : Fin n → Nat) : Equiv (Fin (sum f)) ((i : Fin n) × Fin (f i)) where
  fwd := decodeSigma f
  rev := encodeSigma f
  fwd_eq_iff_rev_eq {k x} := specSigma f k x

def encodePi (f : Fin n → Nat) (x : (i : Fin n) → Fin (f i)) : Fin (prod f) :=
  match n, f, x with
  | 0, _, _ => ⟨0, by simp [prod]⟩
  | _+1, f, x =>
    match encodePi ((f ∘ succ)) (fun ⟨i, hi⟩ => x ⟨i+1, Nat.succ_lt_succ hi⟩) with
    | ⟨k, hk⟩ => Fin.mk (f 0 * k + (x 0).val) $ calc
      _ < f 0 * k + f 0 := Nat.add_lt_add_left (x 0).isLt ..
      _ = f 0 * (k + 1) := Nat.mul_succ ..
      _ ≤ f 0 * prod (f ∘ succ) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk)
      _ = prod f := Eq.symm <| prod_succ ..

def decodePi (f : Fin n → Nat) (k : Fin (prod f)) : (i : Fin n) → Fin (f i) :=
  match n, f, k with
  | 0, _, _ => (nomatch .)
  | n+1, f, ⟨k, hk⟩ =>
    have hf : f 0 > 0 := by
      apply Nat.zero_lt_of_ne_zero
      intro h
      rw [prod_succ, h, Nat.zero_mul] at hk
      contradiction
    have hk' : k / f 0 < prod (f ∘ succ) := by
      rw [Nat.div_lt_iff_lt_mul hf, Nat.mul_comm, ←prod_succ]
      exact hk
    match decodePi ((f ∘ succ)) ⟨k / f 0, hk'⟩ with
    | x => fun
      | ⟨0, _⟩ => ⟨k % f 0, Nat.mod_lt k hf⟩
      | ⟨i+1, hi⟩ => x ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem specPi (f : Fin n → Nat) (k : Fin (prod f)) (x : (i : Fin n) → Fin (f i)) :
  decodePi f k = x ↔ encodePi f x = k := by
    induction n with
    | zero =>
      constructor
      · intro
        match k with
        | ⟨0, _⟩ => rfl
        | ⟨_+1, h⟩ => rw [prod_zero] at h; contradiction
      · intro
        funext ⟨_,_⟩
        contradiction
    | succ n ih =>
      constructor
      · intro h
        match k with
        | ⟨k, hk⟩ =>
          ext
          simp only [encodePi]
          apply Eq.trans (b := f 0 * (k / f 0) + k % f 0)
          · congr 1
            · congr 1
              have hpos : f 0 > 0 := by
                apply Nat.zero_lt_of_ne_zero
                intro hz
                rw [prod_succ, hz, Nat.zero_mul] at hk
                contradiction
              have hk' : k / f 0 < Fin.prod (f ∘ succ) := by
                rw [Nat.div_lt_iff_lt_mul hpos]
                rw [Nat.mul_comm, ←prod_succ]
                exact hk
              have : encodePi (fun i => f (succ i)) (fun i => x (succ i)) = ⟨k / f 0, hk'⟩ := by
                rw [←ih]
                funext i
                rw [←h]
                rfl
              apply Eq.trans (b := (encodePi (fun i => f (succ i)) (fun i => x (succ i))).val)
              · rfl
              · rw [this]
            · rw [←h]
              rfl
          · rw [Nat.add_comm]
            exact Nat.mod_add_div ..
      · intro h
        funext i
        simp only [decodePi]
        split
        next =>
          ext
          simp only
          rw [←h]
          simp only [encodePi]
          rw [Nat.add_comm]
          rw [Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt]
          rfl
          exact (x 0).isLt
        next i hi =>
          match k with
          | ⟨k, hk⟩ =>
            simp only [encodePi] at h
            ext
            have hpos : f 0 > 0 := by
              apply Nat.zero_lt_of_ne_zero
              intro hz
              rw [prod_succ, hz, Nat.zero_mul] at hk
              contradiction
            have hk' : k / f 0 < Fin.prod (f ∘ succ) := by
              rw [Nat.div_lt_iff_lt_mul hpos]
              rw [Nat.mul_comm, ←prod_succ]
              exact hk
            have : decodePi (fun i => f (succ i)) ⟨k / f 0, hk'⟩ = fun i => x (succ i) := by
              rw [ih]
              cases h
              ext
              simp only
              rw [Nat.add_comm]
              rw [Nat.add_mul_div_left _ _ hpos]
              rw [Nat.div_eq_of_lt (x 0).isLt]
              rw [Nat.zero_add]
              rfl
            simp only
            apply Eq.trans (b := (decodePi (fun i => f (succ i)) ⟨k / f 0, hk'⟩ ⟨i, Nat.lt_of_succ_lt_succ hi⟩).val)
            · rfl
            · rw [this]
              rfl

def equivPi (f : Fin n → Nat) : Equiv (Fin (prod f)) ((i : Fin n) → Fin (f i)) where
  fwd := decodePi f
  rev := encodePi f
  fwd_eq_iff_rev_eq {k x} := specPi f k x

def count (p : Fin n → Prop) [DecidablePred p] : Nat :=
  sum fun i => if p i then 1 else 0

def encodeSubtype (p : Fin n → Prop) [inst : DecidablePred p] (i : { i // p i }) : Fin (count p) :=
  match n, p, inst, i with
  | n+1, p, inst, ⟨0, hp⟩ =>
    have : count p > 0 := by simp_arith only [count, sum_succ, if_pos hp]
    ⟨0, this⟩
  | n+1, p, inst, ⟨⟨i+1, hi⟩, hp⟩ =>
    match encodeSubtype (fun i => p (succ i)) ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ with
    | ⟨k, hk⟩ =>
      if h0 : p 0 then
        have : count p = count (p ∘ succ) + 1 := by
          simp_arith only [count, sum_succ, Function.comp_def, if_pos h0]
        this ▸ ⟨k+1, Nat.succ_lt_succ hk⟩
      else
        have : count p = count (p ∘ succ) := by
          simp_arith only [count, sum_succ, if_neg h0, Function.comp_def]
        this ▸ ⟨k, hk⟩

def decodeSubtype (p : Fin n → Prop) [inst : DecidablePred p] (k : Fin (count p)) : { i // p i } :=
  match n, p, inst, k with
  | 0, _, _, ⟨_, h⟩ => False.elim (by simp only [count, sum, foldr_zero] at h; contradiction)
  | n+1, p, inst, ⟨k, hk⟩ =>
    if h0 : p 0 then
      have : count p = count (fun i => p (succ i)) + 1 := by
        simp_arith only [count, sum_succ, if_pos h0]; rfl
      match k with
      | 0 => ⟨0, h0⟩
      | k + 1 =>
        match decodeSubtype (fun i => p (succ i)) ⟨k, Nat.lt_of_add_lt_add_right (this ▸ hk)⟩ with
        | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩
    else
      have : count p = count (fun i => p (succ i)) := by
        simp_arith only [count, sum_succ, if_neg h0]; rfl
      match decodeSubtype (fun i => p (succ i)) ⟨k, this ▸ hk⟩ with
      | ⟨⟨i, hi⟩, hp⟩ => ⟨⟨i+1, Nat.succ_lt_succ hi⟩, hp⟩

theorem specSubtype (p : Fin n → Prop) [inst : DecidablePred p] (k : Fin (count p)) (i : { i // p i }) :
  decodeSubtype p k = i ↔ encodeSubtype p i = k := by
  induction n with
  | zero =>
    simp [count, sum] at k
    cases k
    contradiction
  | succ n ih =>
    constructor
    · intro h
      simp only [decodeSubtype] at h
      split at h
      next h0 =>
        have : count p = count (fun i => p (succ i)) + 1 := by
          simp_arith only [count, sum_succ, if_pos h0]; rfl
        split at h
        next =>
          cases h
          ext
          apply Eq.symm
          assumption
        next heq _ =>
          cases h
          ext
          simp only [encodeSubtype, dif_pos h0, congr_ndrec @Fin.val]
          match k with
          | ⟨0, _⟩ => contradiction
          | ⟨k+1, hk⟩ =>
            injection heq with hkk
            congr 1
            apply Eq.trans (b := (Fin.mk k (Nat.lt_of_succ_lt_succ (this ▸ hk))).val)
            · apply Fin.val_eq_of_eq
              simp only [Nat.add_eq, Nat.add_zero, Fin.eta]
              rw [←ih]
              congr
            · rfl
      next h0 =>
        have : count p = count (fun i => p (succ i)) := by
          simp_arith only [count, sum_succ, if_neg h0]; rfl
        match k, i with
        | ⟨_, _⟩, ⟨⟨0, _⟩, _⟩ => contradiction
        | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
          ext
          simp only [encodeSubtype, dif_neg h0, congr_ndrec @Fin.val]
          simp only at h
          apply Eq.trans (b := (Fin.mk k (this ▸ hk)).val)
          · apply Fin.val_eq_of_eq
            rw [←ih]
            cases h
            rfl
          · rfl
    · intro h
      simp only [decodeSubtype]
      split
      next h0 =>
        have : count p = count (fun i => p (succ i)) + 1 := by
          simp_arith only [count, sum_succ, if_pos h0]; rfl
        split
        next heq _ =>
          match k, i with
          | ⟨_,_⟩, ⟨⟨0,_⟩, _⟩ => rfl
          | ⟨k,hk⟩, ⟨⟨i+1,hi⟩, hp⟩ =>
            cases heq
            simp only [encodeSubtype, dif_pos h0] at h
            have h := val_eq_of_eq h
            rw [congr_ndrec @Fin.val] at h
            contradiction
        next k' hk' heq _ =>
          match k, i with
          | ⟨_,_⟩, ⟨⟨0, _⟩, _⟩ =>
            simp only [encodeSubtype] at h
            cases h
            contradiction
          | ⟨k,hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
            cases heq
            have : decodeSubtype (fun i => p (succ i)) ⟨k', Nat.lt_of_add_lt_add_right (this ▸ hk')⟩ = ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ := by
              rw [ih]
              simp only [encodeSubtype, dif_pos h0] at h
              let h := val_eq_of_eq h
              rw [congr_ndrec @Fin.val] at h
              cases h
              rfl
            congr
            apply Eq.trans (b := (⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ : { i // p (succ i) }).val.val)
            · apply congrArg Fin.val
              apply congrArg Subtype.val
              simp only [Nat.add_eq, Nat.add_zero, ih]
              have h := Fin.val_eq_of_eq h
              simp only [encodeSubtype, dif_pos h0, congr_ndrec @Fin.val] at h
              cases h
              rfl
            · rfl
      next h0 =>
        match k, i with
        | ⟨k, hk⟩, ⟨⟨0, _⟩, hp⟩ =>
          contradiction
        | ⟨k, hk⟩, ⟨⟨i+1, hi⟩, hp⟩ =>
          congr
          apply Eq.trans (b := (⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, hp⟩ : { i // p (succ i) }).val.val)
          · apply congrArg Fin.val
            apply congrArg Subtype.val
            simp only [Nat.add_eq, Nat.add_zero, ih]
            ext
            have h := Fin.val_eq_of_eq h
            simp only [encodeSubtype, dif_neg h0, congr_ndrec @Fin.val] at h
            cases h
            rfl
          · rfl

def equivSubtype (p : Fin n → Prop) [DecidablePred p] : Equiv (Fin (count p)) { i // p i } where
  fwd := decodeSubtype p
  rev := encodeSubtype p
  fwd_eq_iff_rev_eq {k x} := specSubtype p k x

abbrev repr (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin n) : Prop :=
  Find.find? (s.r i) = some i

def quot (s : Setoid (Fin n)) [DecidableRel s.r] : Nat := count (repr s)

private def getRepr (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin n) : Fin (quot s) :=
    match h : Find.find? (s.r i) with
    | some j =>
      have : repr s j := by
        have hij : i ≈ j := Find.of_find?_eq_some _ h
        unfold repr
        rw [←h]
        congr
        funext k
        rw [decide_eq_decide]
        constructor
        · intro hjk
          apply Setoid.trans (b := j)
          · exact hij
          · exact hjk
        · intro hik
          apply Setoid.trans (b := i)
          · apply Setoid.symm
            exact hij
          · exact hik
      encodeSubtype (repr s) ⟨j, this⟩
    | none => absurd (Find.not_of_find?_eq_none i h) $ by
      intro h
      apply h
      exact Setoid.refl ..

private theorem getRepr_eq_getRepr_of_equiv (s : Setoid (Fin n)) [DecidableRel s.r] {{i j : Fin n}} : s.r i j → getRepr s i = getRepr s j := by
  intro hij
  unfold getRepr
  split
  · next i' hi' =>
    split
    · next j' hj' =>
      simp only
      congr
      apply Option.some.inj
      rw [←hi', ←hj']
      congr
      funext k
      rw [decide_eq_decide]
      constructor
      · intro hik
        apply Setoid.trans (b := i)
        · apply Setoid.symm
          exact hij
        · exact hik
      · intro hjk
        apply Setoid.trans (b := j)
        · exact hij
        · exact hjk
    · next h =>
      absurd (Find.not_of_find?_eq_none j h)
      exact Setoid.refl ..
  · next h =>
    absurd (Find.not_of_find?_eq_none i h)
    exact Setoid.refl ..

private theorem subtype_eq_of_val_equiv_val (s : Setoid (Fin n)) [DecidableRel s.r] {{i j : Subtype (repr s)}} : s.r i.val j.val → i = j := by
  intro hij
  match i, j with
  | ⟨i, hri⟩, ⟨j, hrj⟩ =>
    unfold repr at hri hrj
    apply Subtype.eq
    apply Option.some.inj
    rw [←hri, ←hrj]
    congr
    funext k
    rw [decide_eq_decide]
    constructor
    · intro hik
      apply Setoid.trans (b := i)
      · apply Setoid.symm
        exact hij
      · exact hik
    · intro hjk
      apply Setoid.trans (b := j)
      · exact hij
      · exact hjk

def encodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (i : Quotient s) : Fin (quot s) :=
  Quotient.liftOn i (getRepr s) (getRepr_eq_getRepr_of_equiv s)

def decodeQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (i : Fin (quot s)) : Quotient s :=
  Quotient.mk s (decodeSubtype (repr s) i)

theorem specQuotient (s : Setoid (Fin n)) [DecidableRel s.r] (k : Fin (quot s)) (i : Quotient s) :
  decodeQuotient s k = i ↔ encodeQuotient s i = k := by
  induction i using Quotient.inductionOn with
  | _ i =>
  unfold decodeQuotient encodeQuotient
  constructor
  · intro h
    have h := Quotient.exact h
    apply Eq.trans (b := getRepr s i)
    · rfl
    · unfold getRepr
      split
      · next j hj =>
        rw [←specSubtype]
        have hij : i ≈ j := Find.of_find?_eq_some _ hj
        apply subtype_eq_of_val_equiv_val
        apply Setoid.trans (b := i)
        · exact h
        · exact hij
      · next hnone =>
        absurd (Find.not_of_find?_eq_none i hnone)
        exact Setoid.refl ..
  · intro h
    have h : getRepr s i = k := h
    apply Quotient.sound
    unfold getRepr at h
    split at h
    · next j hj =>
      rw [←specSubtype] at h
      rw [h]
      apply Setoid.symm
      exact Find.of_find?_eq_some j hj
    · next hnone =>
      absurd (Find.not_of_find?_eq_none i hnone)
      exact Setoid.refl ..

def equivQuotient (s : Setoid (Fin n)) [DecidableRel s.r] : Equiv (Fin (quot s)) (Quotient s) where
  fwd := decodeQuotient s
  rev := encodeQuotient s
  fwd_eq_iff_rev_eq {k i} := specQuotient s k i

end Fin
