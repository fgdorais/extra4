
/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace List

@[elab_as_elim]
def recDiagAux {motive : List α → List β → Sort _}
  (left : (xs : List α) → motive xs [])
  (right : (ys : List β) → motive [] ys)
  (diag : {xs : List α} → {ys : List β} → motive xs ys → ∀ x y, motive (x :: xs) (y :: ys)) :
  (xs : List α) → (ys : List β) → motive xs ys
  | _, [] => left _
  | [], _ => right _
  | x::xs, y::ys => diag (recDiagAux left right diag xs ys) x y

/-- Diagonal recursor for pairs of lists -/
@[elab_as_elim]
def recDiag {motive : List α → List β → Sort _}
    (nil_nil : motive [] [])
    (nil_cons : {ys : List β} → motive [] ys → {y : β} → motive [] (y::ys))
    (cons_nil : {xs : List α} → motive xs [] → {x : α} → motive (x::xs) [])
    (cons_cons : {xs : List α} → {ys : List β} → motive xs ys → ∀ x y, motive (x::xs) (y::ys))
    (xs : List α) (ys : List β) : motive xs ys :=
  recDiagAux left right cons_cons xs ys
where
  left
  | [] => nil_nil
  | _::_ => cons_nil (left _)
  right
  | [] => nil_nil
  | _::_ => nil_cons (right _)

@[elab_as_elim, inherit_doc recDiag]
def recDiagOn {motive : List α → List β → Sort _} (xs : List α) (ys : List β)
    (nil_nil : motive [] [])
    (nil_cons : {ys : List β} → motive [] ys → {y : β} → motive [] (y::ys))
    (cons_nil : {xs : List α} → motive xs [] → {x : α} → motive (x::xs) [])
    (cons_cons : {xs : List α} → {ys : List β} → motive xs ys → ∀ x y, motive (x::xs) (y::ys)) :
    motive xs ys := recDiag nil_nil nil_cons cons_nil cons_cons xs ys

@[elab_as_elim, inherit_doc recDiag]
def casesDiagOn {motive : List α → List β → Sort _} (xs : List α) (ys : List β)
      (nil_nil : motive [] [])
      (nil_cons : {ys : List β} → {y : β} → motive [] (y::ys))
      (cons_nil : {xs : List α} → {x : α} → motive (x::xs) [])
      (cons_cons : {xs : List α} → {ys : List β} → ∀ x y, motive (x::xs) (y::ys)) :
    motive xs ys :=
      recDiag nil_nil (fun _ _ => nil_cons) (fun _ _ => cons_nil) (fun _ _ _ => cons_cons _ _) xs ys
