import Extra.Index.Basic

namespace List

theorem reverseAux_step (z : α) (xs ys : List α) : List.reverseAux (z :: xs) ys = List.reverseAux xs (z :: ys) := rfl

namespace Index

def reverseAux : {xs ys : List α} → Sum (Index xs) (Index ys) → Index (List.reverseAux xs ys)
  | [], _, .inr j => j
  | x :: xs, ys, .inl .head => (List.reverseAux_step x xs ys).symm ▸ reverseAux (.inr .head)
  | x :: xs, ys, .inl (.tail i) => (List.reverseAux_step x xs ys).symm ▸ reverseAux (.inl i)
  | x :: xs, ys, .inr j => (List.reverseAux_step x xs ys).symm ▸ reverseAux (.inr (.tail j))

def reverseTR {xs : List α} (i : Index xs) : Index xs.reverse := reverseAux (.inl i)

def appendTR {xs ys : List α} : Sum (Index xs) (Index ys) → Index (List.append xs ys)
  | .inl i => List.append_eq_appendTR ▸ reverseAux (.inl i.reverseTR)
  | .inr j => List.append_eq_appendTR ▸ reverseAux (.inr j)
