/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace FloatArray

@[extern "lean_sarray_size", simp]
def usize (a : @& FloatArray) : USize := a.size.toUSize

@[inline]
unsafe def mapMUnsafe [Monad m] (a : FloatArray) (f : Float → m Float) : m FloatArray :=
  loop a 0 a.usize
where
  @[specialize]
  loop (a : FloatArray) (k s : USize) := do
    if k < s then
      let x := a.uget k lcProof
      let y ← f x
      let a := a.uset k y lcProof
      loop a (k+1) s
    else pure a

@[implemented_by mapMUnsafe]
def mapM [Monad m] (a : FloatArray) (f : Float → m Float) : m FloatArray := do
  let mut r := a
  for i in [0:r.size] do
    r := r.set! i (← f r[i]!)
  return r

@[inline]
def map [Monad m] (a : FloatArray) (f : Float → Float) : FloatArray :=
  mapM (m:=Id) a f
