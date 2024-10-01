/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Batteries

/--
The `CountReaderT ρ m` monad transformer stores a read-only state of type `ρ` and keeps a count of
the number of times the state is read.
-/
def CountReaderT (ρ : Type _) (m : Type _ → Type _) := StateT Nat <| ReaderT ρ m

/--
The `CountReaderM ρ` monad stores a read-only state of type `ρ` and keeps a count of the number of
times the state is read.
-/
abbrev CountReaderM (ρ : Type _) := CountReaderT ρ Id

instance (ρ m) [Monad m] : Monad (CountReaderT ρ m) :=
  inferInstanceAs (Monad (StateT _ _))

/--
`CountReaderT.run x r` runs the monad `x` with state `r` and starting counter zero.
-/
@[inline] protected def CountReaderT.run [Monad m] (x : CountReaderT ρ m α) (r : ρ) (n := 0) :
    m (α × Nat) := x n r

/--
`CountReaderM.run x r` runs the monad `x` with state value `r` and starting counter zero.
-/
@[inline] protected def CountReaderM.run (x : CountReaderM ρ α) (r : ρ) : α × Nat := x 0 r

namespace CountReaderT

/-- `reset` resets the counter value of the `CountReaderT ρ m` monad to zero. -/
@[inline] def reset [Monad m] : CountReaderT ρ m PUnit := StateT.set 0

/-- `count` reads the current counter value of the `CountReaderT ρ m` monad. -/
@[inline] def count [Monad m] : CountReaderT ρ m Nat := StateT.get

/-- `read` reads the value of the `CountReaderT ρ m` monad, incrementing the read counter. -/
@[inline] def read [Monad m] : CountReaderT ρ m ρ := fun c x => pure (x, c+1)

instance (ρ m) [Monad m] : MonadReader ρ (CountReaderT ρ m) where
  read := read

end CountReaderT

/--
The `CountStateT σ m` monad transformer stores a state of type `σ` and keeps count of the number
of times the state is read and written.
-/
def CountStateT (σ : Type _) := StateT (σ × Nat × Nat)

/--
The `CountStateM σ` monad stores a state of type `σ` and keeps a count of the number of the number
of times the state is read and written.
-/
abbrev CountStateM (σ : Type _) := CountStateT σ Id

instance (σ m) [Monad m] : Monad (CountStateT σ m) := inferInstanceAs (Monad (StateT _ _))

/-- `CountStateT.run x s` runs the monad `x` with initial state `s` and starting counters zero. -/
@[inline] protected def CountStateT.run [Monad m] (x : CountStateT σ m α) (s : σ) :
    m (α × σ × Nat × Nat) := x (s, 0, 0)

/-- `CountStateM.run x s` runs the monad `x` with initial state `s` and starting counters zero. -/
@[inline] protected def CountStateM.run (x : CountStateM σ α) (s : σ) :
    α × σ × Nat × Nat := x (s, 0, 0)

namespace CountStateT

/-- `get s` reads the state of the `CountStateT σ m` monad, incrementing the read counter. -/
@[inline] def get [Monad m] : CountStateT σ m σ := do
  let (s, r, w) ← StateT.get
  StateT.set (s, r+1, w)
  return s

/-- `set s` sets the state `CountStateT σ m` monad to `s`, incrementing the write counter. -/
@[inline] def set [Monad m] (s : σ) : CountStateT σ m PUnit := do
  let (_, r, w) ← StateT.get
  StateT.set (s, r, w+1)

/--
`modifyGet f` applies the function `f` to the current state, updates the state, returns the
computed value, incrementing the read and write counters.
-/
@[inline] def modifyGet [Monad m] (f : σ → α × σ) : CountStateT σ m α :=
  StateT.modifyGet fun (s, r, w) => match f s with | (x, s) => (x, s, r+1, w+1)

/-- `counts` reads the current read/write counters of the `CountStateT σ m` monad. -/
@[inline] def counts [Monad m] : CountStateT σ m (Nat × Nat) := do
  let (_, r, w) ← StateT.get
  return (r, w)

/-- `readCount` reads the current read counter of the `CountStateT σ m` monad. -/
@[inline] def readCount [Monad m] : CountStateT σ m Nat := do
  let (_, r, _) ← StateT.get
  return r

/-- `writeCount` reads the current write counter of the `CountStateT σ m` monad. -/
@[inline] def writeCount [Monad m] : CountStateT σ m Nat := do
  let (_, _, w) ← StateT.get
  return w

/-- `reset` resets the read/write counters of the `CountStateT ρ m` state to zero. -/
@[inline] def reset [Monad m] : CountStateT σ m PUnit := do
  StateT.set (← get, 0, 0)

instance (σ m) [Monad m] : MonadState σ (CountStateT σ m) where
  get := get
  set := set
  modifyGet := modifyGet

end CountStateT
