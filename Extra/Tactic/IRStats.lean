/-
Copyright © 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Reference: https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/tail.20recursion/near/404515501
-/
import Lean
open Lean

partial def visitBody (f : IR.FunId) : IR.FnBody → StateM (NameSet × Bool) Unit
  | .vdecl x _ e b => do
    let tailcall := match b with | .ret (.var y) => x == y | _ => false
    match e with
    | .fap c _ =>
      if tailcall && c == f then modify fun (s, _) => (s, true)
      else modify fun (s, b) => (s.insert c, b)
    | .pap c _ => modify fun (s, b) => (s.insert c, b)
    | _ => pure ()
    visitBody f b
  | .jdecl _ _ v b => do visitBody f v; visitBody f b
  | .case _ _ _ cs => for c in cs do visitBody f c.body
  | e => if e.isTerminal then pure () else visitBody f e.body

elab "#ir_stats " decl:ident : command => do
  let name := decl.getId
  let some decl := (IR.declMapExt.getState (← getEnv)).find? name
    | throwError "IR declaration {name} not found"
  match decl with
  | .extern .. => logInfo m!"{name} is external"
  | .fdecl (f := f) (body := b) .. =>
    let (_, calls, tailRec) := (visitBody f b).run ({}, false)
    if !calls.isEmpty then
      logInfo m!"{name} calls (recursively) {calls.toList}"
    if tailRec then
      logInfo m!"{name} is tail-recursive"
    else if calls.contains f then
      logInfo m!"{name} is properly recursive"
    else
      logInfo m!"{name} is not recursive"

@[specialize] def map {α β} (f : α → β) : List α → List β
  | []    => []
  | a::as => f a :: map f as

@[inline] def mapTR {α β} (f : α → β) (as : List α) : List β :=
  loop as []
where
  @[specialize] loop : List α → List β → List β
  | [],    bs => bs.reverse
  | a::as, bs => loop as (f a :: bs)

#ir_stats map._rarg -- map._rarg is properly recursive
#ir_stats mapTR.loop._rarg -- mapTR.loop._rarg is tail-recursive
