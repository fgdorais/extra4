/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Basic

namespace ByteArray

@[extern "lean_sarray_size", simp]
def usize (a : @& ByteArray) : USize := a.size.toUSize

@[inline]
unsafe def mapMUnsafe [Monad m] (a : ByteArray) (f : UInt8 → m UInt8) : m ByteArray :=
  loop a 0 a.usize
where
  @[specialize]
  loop (a : ByteArray) (k s : USize) := do
    if k < a.usize then
      let x := a.uget k lcProof
      let y ← f x
      let a := a.uset k y lcProof
      loop a (k+1) s
    else pure a

@[implemented_by mapMUnsafe]
def mapM [Monad m] (a : ByteArray) (f : UInt8 → m UInt8) : m ByteArray := do
  let mut r := a
  for i in [0:r.size] do
    r := r.set! i (← f r[i]!)
  return r

@[inline]
def map [Monad m] (a : ByteArray) (f : UInt8 → UInt8) : ByteArray :=
  mapM (m:=Id) a f
