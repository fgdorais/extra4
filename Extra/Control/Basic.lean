import Extra.Basic

@[simp] theorem id_map_fun [Functor F] [LawfulFunctor F] :
    Functor.map (f := F) (α := α) id = id := by
  funext; simp

@[simp] theorem comp_map_fun [Functor F] [LawfulFunctor F] (f : α → β) (g : β → γ) :
    Functor.map (f := F) (g ∘ f) = Functor.map (f := F) g ∘ Functor.map (f := F) f := by
  funext; simp; rfl

instance (F G) [Functor F] [Functor G] : Functor (G ∘ F) where
  map f x := ((f <$> ·) <$> x : G _)

instance (F G) [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] : LawfulFunctor (G ∘ F) where
  map_const := rfl
  id_map := by simp [Functor.map]
  comp_map := by simp [Functor.map]

structure NaturalTransformation (F G : Type _ → Type _) where
  app {{α}} : F α → G α

class LawfulNaturalTransformation [Functor F] [Functor G] (η : NaturalTransformation F G) where
  app_map_eq_map_app (f : α → β) (x : F α) : η.app (f <$> x) = f <$> η.app x

export LawfulNaturalTransformation (app_map_eq_map_app)

def NaturalTransformation.identity : NaturalTransformation F F where
  app _ := id

instance [Functor F] : LawfulNaturalTransformation (NaturalTransformation.identity (F := F)) where
  app_map_eq_map_app _ _ := rfl

def NaturalTransformation.compose (η : NaturalTransformation G H) (ε : NaturalTransformation F G) :
    NaturalTransformation F H where
  app _ x := η.app (ε.app x)

instance (η : NaturalTransformation G H) (ε : NaturalTransformation F G)
    [Functor F] [Functor G] [Functor H]
    [LawfulNaturalTransformation η] [LawfulNaturalTransformation ε] :
    LawfulNaturalTransformation (NaturalTransformation.compose η ε) where
  app_map_eq_map_app _ _ := by simp [NaturalTransformation.compose, app_map_eq_map_app]

structure NaturalIsomorphism (F G : Type _ → Type _) extends NaturalTransformation F G where
  inv {{α}} : G α → F α

class LawfulNaturalIsomorphism [Functor F] [Functor G] (η : NaturalIsomorphism F G)
    extends LawfulNaturalTransformation η.toNaturalTransformation where
  app_inv (x : G α) : η.app (η.inv x) = x
  inv_app (x : F α) : η.inv (η.app x) = x
  inv_map_eq_map_inv (f : α → β) (x : G α) : η.inv (f <$> x) = f <$> η.inv x

export LawfulNaturalIsomorphism (app_inv inv_app inv_map_eq_map_inv)

protected def NaturalIsomorphism.inverse (η : NaturalIsomorphism F G) : NaturalIsomorphism G F where
  app := η.inv
  inv := η.app

instance [Functor F] [Functor G] (η : NaturalIsomorphism F G) [LawfulNaturalIsomorphism η] :
    LawfulNaturalIsomorphism η.inverse where
  app_inv := inv_app
  inv_app := app_inv
  app_map_eq_map_app := inv_map_eq_map_inv
  inv_map_eq_map_inv := app_map_eq_map_app
