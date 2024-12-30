import Extra.Control.Basic

namespace Control

@[ext] structure Ran (F G) [Functor F] [Functor G] (α : Type _) where
  run : (α → F ω) → G ω
  map_run_eq_run_map (f : ω → ω') (t : α → F ω) : f <$> run t = run fun x => f <$> t x

namespace Ran

instance (F G) [Functor F] [Functor G] : Functor (Ran F G) where
  map f x := {
    run t := x.run fun x => t (f x)
    map_run_eq_run_map f t := by simp only [x.map_run_eq_run_map]
  }

instance (F G) [Functor F] [Functor G] : LawfulFunctor (Ran F G) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

def counit (F G) [Functor F] [Functor G] : NaturalTransformation (Ran F G ∘ F) G where
  app _ x := x.run id

instance (F G) [Functor F] [Functor G] : LawfulNaturalTransformation (counit F G) where
  app_map_eq_map_app f x := by simp [counit, map_run_eq_run_map, Functor.map]

def univ [Functor F] [Functor G] [Functor H] [LawfulFunctor H] (η : NaturalTransformation (H ∘ F) G)
    [LawfulNaturalTransformation η] : NaturalTransformation H (Ran F G) where
  app α x := {
    run t := η.app (t <$> x : H (F _))
    map_run_eq_run_map f t := by
      rw [← LawfulNaturalTransformation.app_map_eq_map_app]
      simp [Functor.map]
  }

instance [Functor F] [Functor G] [Functor H] [LawfulFunctor H]
    (η : NaturalTransformation (H ∘ F) G) [LawfulNaturalTransformation η] :
    LawfulNaturalTransformation (univ η) where
  app_map_eq_map_app f x := by simp [univ, Functor.map]

@[simp] theorem univ_counit [Functor F] [Functor G] [Functor H] (x : Ran F G α):
  (univ (counit F G)).app x = x := rfl

@[simp] theorem counit_univ [Functor F] [Functor G] [Functor H] [LawfulFunctor H] (η : NaturalTransformation (H ∘ F) G)
    [LawfulNaturalTransformation η] (x : H (F α)) : (counit F G).app ((univ η).app x) = η.app x := by
  simp [counit, univ]
