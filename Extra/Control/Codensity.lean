import Extra.Control.Ran

namespace Control

abbrev Codensity (F) [Functor F] := Ran F F

protected def Codensity.pure [Functor F] (x : α) : Codensity F α where
  run t := t x
  map_run_eq_run_map _ _ := rfl

protected def Codensity.bind [Functor F] (x : Codensity F α) (f : α → Codensity F β) :
    Codensity F β where
  run t := x.run fun x => (f x).run t
  map_run_eq_run_map _ _ := by simp [Ran.map_run_eq_run_map]

instance [Functor F] : Monad (Codensity F) where
  pure := Codensity.pure
  bind := Codensity.bind

instance [Functor F] : LawfulMonad (Codensity F) where
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_seq _ _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
