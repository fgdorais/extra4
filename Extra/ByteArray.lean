/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic
import Extra.Array

namespace ByteArray

@[simp] theorem append_eq (as bs : ByteArray) : ByteArray.append as bs = as ++ bs := rfl

theorem getElem_eq_data_getElem (as : ByteArray) (h : i < as.size) : as[i] = as.data[i] := rfl

@[simp] theorem empty_data : empty.data = #[] := rfl

@[simp] theorem size_empty : empty.size = 0 := rfl

theorem copySlice_data (as i bs j len exact) :
  (copySlice as i bs j len exact).data = bs.data.extract 0 j ++ as.data.extract i (i + len)
    ++ bs.data.extract (j + min len (as.data.size - i)) bs.data.size := rfl

theorem append_data (as bs : ByteArray) : (as ++ bs).data = as.data ++ bs.data := by
  conv => lhs; simp [HAppend.hAppend, Append.append, ByteArray.append]
  simp [copySlice, size, Array.extract_all]
  rw [as.data.extract_empty_of_stop_le_start (Nat.le_add_right ..), Array.append_nil]

theorem size_append (as bs : ByteArray) : (as ++ bs).size = as.size + bs.size := by
  simp [size, append_data, Array.size_append]

theorem get_append_left {as bs : ByteArray} (hlt : i < as.size)
    (h : i < (as ++ bs).size := size_append .. ▸ Nat.lt_of_lt_of_le hlt (Nat.le_add_right ..)) :
    (as ++ bs)[i] = as[i] := by
  simp [getElem_eq_data_getElem, append_data, Array.get_append_left hlt]

theorem get_append_right {as bs : ByteArray} (hle : as.size ≤ i) (h : i < (as ++ bs).size)
    (h' : i - as.size < bs.size := Nat.sub_lt_left_of_lt_add hle (size_append .. ▸ h)) :
    (as ++ bs)[i] = bs[i - as.size] := by
  simp [getElem_eq_data_getElem, append_data, Array.get_append_right hle]; rfl

theorem extract_data (as : ByteArray) (start stop : Nat) :
    (as.extract start stop).data = as.data.extract start stop := by
  simp [extract, copySlice]
  match Nat.le_total start stop with
  | .inl h => rw [Nat.add_sub_cancel' h]
  | .inr h =>
    rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]
    rw [Array.extract_empty_of_stop_le_start _ h]
    rw [Array.extract_empty_of_stop_le_start _ (Nat.le_refl _)]

theorem size_extract (as : ByteArray) (start stop : Nat) :
    (as.extract start stop).size = min stop as.size - start := by
  simp [size, extract_data, Array.size_extract]

theorem get_extract_aux {as : ByteArray} {start stop : Nat} (h : i < (as.extract start stop).size) :
    start + i < as.size := by
  apply Nat.add_lt_of_lt_sub'
  apply Nat.lt_of_lt_of_le h
  rw [size_extract, ← Nat.sub_min_sub_right]
  exact Nat.min_le_right ..

theorem get_extract {as : ByteArray} {start stop : Nat} (h : i < (as.extract start stop).size)
    (h' : start + i < as.size := get_extract_aux h) :
    (as.extract start stop)[i] = as[start+i] := by
  simp [getElem_eq_data_getElem]
  trans ((as.data.extract start stop)[i]'(extract_data .. ▸ h))
  · congr 1; exact extract_data ..
  · exact Array.get_extract ..
