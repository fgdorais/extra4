import Batteries

abbrev Matrix (α rows cols) := Vector (Vector α cols) rows

namespace Matrix

protected abbrev size (_ : Matrix α r c) := (r, c)

protected abbrev row (m : Matrix α r c) (i) (h : i < r := by get_elem_tactic) : Vector α c := m[i]

@[inline] protected def col (m : Matrix α r c) (i) (h : i < c := by get_elem_tactic) : Vector α r :=
  .ofFn fun j => m[j][i]

@[simp] theorem getElem_row (m : Matrix α r c) (i j) (hi : i < r) (hj : j < c) :
    (m.row i)[j] = m[i][j] := rfl

@[simp] theorem getElem_col (m : Matrix α r c) (i j) (hi : i < r) (hj : j < c) :
    (m.col j)[i] = m[i][j] := by
  simp [Matrix.col]

@[inline] protected def ofFn (f : Fin r → Fin c → α) : Matrix α r c :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

@[simp] theorem getElem_ofFn (f : Fin r → Fin c → α) (i j) (hi : i < r) (hj : j < c) :
    (Matrix.ofFn f)[i][j] = f ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [Matrix.ofFn]

@[inline] def transpose (m : Matrix α c r) : Matrix α r c :=
  .ofFn fun i j => m[j][i]

@[simp] theorem getElem_transpose (m : Matrix α c r) (i j) (hi : i < r) (hj : j < c) :
    m.transpose[i][j] = m[j][i] := by
  simp [transpose]

@[inline] protected def mulVec (dot : Vector α c → Vector α c → α) (m : Matrix α r c) (v : Vector α c) : Vector α r :=
  .ofFn fun i => dot m[i] v

@[simp] theorem getElem_mulVec (m : Matrix α r c) (v : Vector α c) (i) (h : i < r) :
    (m.mulVec dot v)[i] = dot m[i] v := by
  simp [Matrix.mulVec]

@[inline] protected def mul (dot : Vector α k → Vector α k → α) (m : Matrix α r k) (n : Matrix α k c) :
    Matrix α r c := Matrix.ofFn fun i j => dot (m.row i) (n.col j)

@[inline] def diag [Zero α] (d : Vector α n) : Matrix α n n :=
  Matrix.ofFn fun i j => if i = j then d[i] else 0

@[simp] theorem getElem_diag_ne [Zero α] (d : Vector α n) (i j) (h : i ≠ j) (hi : i < n) (hj : j < n) :
    (diag d)[i][j] = 0 := by
  simp [diag, h]

@[simp] theorem getElem_diag_eq [Zero α] (d : Vector α n) (i) (hi : i < n) :
    (diag d)[i][i] = d[i] := by
  simp [diag]

theorem getElem_diag [Zero α] (d : Vector α n) (i j) (hi : i < n) (hj : j < n) :
    (diag d)[i][j] = if i = j then d[i] else 0 := by
  simp [diag]
