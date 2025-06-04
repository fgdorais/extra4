import Extra.Control.Basic

namespace Control

structure Adjunction (L R : Type _ → Type _) where
  protected left : (L α → β) → α → R β
  protected right : (α → R β) → L α → β

protected def Adjunction.unit (adj : Adjunction L R) : NaturalTransformation Id (R ∘ L) where
  app {α} (x : α) := adj.left id x

protected def Adjunction.counit (adj : Adjunction L R) : NaturalTransformation (L ∘ R) Id where
  app {α} (x : L (R α)) := adj.right id x

theorem unit_eq_left_id (adj : Adjunction L R) (x : α) :
    adj.unit.app x = adj.left id x := rfl

theorem counit_eq_right_id (adj : Adjunction L R) (x : L (R α)) :
    adj.counit.app x = adj.right id x := rfl

class LawfulAdjunction [Functor L] [Functor R] (adj : Adjunction L R) : Prop where
  left_right (f : α → R β) : adj.left (adj.right f) = f
  right_left (g : L α → β) : adj.right (adj.left g) = g
  unit_comp_eq_map_unit (f : α → β) (x) : adj.unit.app (f x) = f <$> adj.unit.app x
  comp_counit_eq_map_counit (f : α → β) (x) : f (adj.counit.app x) = adj.counit.app (f <$> x)
  counit_map_unit (x : R α) : adj.counit.app (α := α) <$> (adj.unit.app x : R (L (R α))) = x
  counit_unit_map (x : L α) : adj.counit.app (adj.unit.app (α := α) <$> x : L (R (L α))) = x

export LawfulAdjunction (left_right right_left unit_comp_eq_map_unit comp_counit_eq_map_counit
  counit_map_unit counit_unit_map)

attribute [simp] left_right right_left counit_map_unit counit_unit_map

theorem left_eq_iff_eq_right [Functor L] [Functor R] {adj : Adjunction L R} [LawfulAdjunction adj]
    {f : L α → β} {g : α → R β} : adj.left f = g ↔ f = adj.right g := by
  constructor
  · intro h; rw [← h, right_left]
  · intro h; rw [h, left_right]

instance (adj : Adjunction L R) [Functor L] [Functor R] [LawfulAdjunction adj] :
    LawfulNaturalTransformation adj.unit where
  app_map_eq_map_app _ _ := by simp [Function.comp_apply, unit_comp_eq_map_unit]; rfl

instance (adj : Adjunction L R) [Functor L] [Functor R] [LawfulAdjunction adj] :
    LawfulNaturalTransformation adj.counit where
  app_map_eq_map_app _ _ := by simp [Functor.map, comp_counit_eq_map_counit]
