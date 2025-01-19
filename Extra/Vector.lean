import Extra.Array

namespace Vector

@[simp] theorem cast_self (v : Vector α n) (h : n = n) : v.cast h = v := rfl

@[simp] theorem cast_cast (v : Vector α n) (h₁ : n = m) (h₂ : m = k) :
    (v.cast h₁).cast h₂ = v.cast (Eq.trans h₁ h₂) := rfl

theorem getElem_eq_getElem_toArray (v : Vector α n) (i) (h : i < n) :
    v[i] = v.toArray[i]'(v.size_toArray.symm ▸ h) := rfl

@[simp] theorem get_eq_getElem (v : Vector α n) (i : Fin n) : v.get i = v[i.val] := rfl

@[simp] theorem uget_eq_getElem (v : Vector α n) (i : USize) (h : i.toNat < n) :
    v.uget i h = v[i.toNat] := rfl

theorem getElem_set (v : Vector α n) (i : Fin n) (j) (x : α) (h : j < n) :
    (v.set i x)[j] = if i = j then x else v[j] := by
  cases v; simp [Array.getElem_set]
