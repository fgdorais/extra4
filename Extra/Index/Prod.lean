import Extra.Index.Basic
import Extra.Index.Bind
import Extra.Index.Map

namespace List

namespace Index
variable {α β} {xs : List α} {ys : List β}

def prod : Index xs × Index ys → Index (List.product xs ys)
| (i,j) => Index.bind (λ x => ys.map (Prod.mk x)) ⟨i, j.map (Prod.mk i.val)⟩

def unprod (k : Index (List.product xs ys)) : Index xs × Index ys :=
  match unbind (λ x => ys.map (Prod.mk x)) k with
  | ⟨i,j⟩ => (i, j.unmap (Prod.mk i.val))

theorem unprod_prod (i : Index xs × Index ys) : unprod (prod i) = i := by
  simp only [prod, unprod]
  rw [unbind_bind, unmap_map]

theorem prod_unprod (k : Index (List.product xs ys)) : prod (unprod k) = k := by
  simp only [prod, unprod]
  rw [map_unmap, bind_unbind]

theorem prod_eq_iff_eq_unprod (i : Index xs × Index ys) (k : Index (List.product xs ys)) : prod i = k ↔ i = unprod k := by
  constructor
  · intro h; rw [←h, unprod_prod]
  · intro h; rw [h, prod_unprod]

theorem unprod_eq_iff_eq_prod (i : Index (List.product xs ys)) (j : Index xs × Index ys) : unprod i = j ↔ i = prod j := by
  constructor
  · intro h; rw [←h, prod_unprod]
  · intro h; rw [h, unprod_prod]

def prodEquiv (xs ys : List α) : Equiv (Index xs × Index ys) (Index (List.product xs ys)) where
  fwd := prod
  rev := unprod
  fwd_eq_iff_rev_eq := by
    intros
    constructor
    · intro | rfl => exact unprod_prod ..
    · intro | rfl => exact prod_unprod ..

theorem val_prod (i : Index xs × Index ys) : (prod i).val = (i.fst.val, i.snd.val) := by
  rw [prod, val_bind, val_map]

theorem val_unprod (i : Index (List.product xs ys)) : ((unprod i).fst.val, (unprod i).snd.val) = i.val := by
  rw [←prod_unprod i, val_prod, unprod_prod]
