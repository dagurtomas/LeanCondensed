import Mathlib.Topology.Category.LightProfinite.Basic

universe u

open CategoryTheory Limits Opposite FintypeCat

namespace LightProfinite

instance hasForget₂ : HasForget₂ LightProfinite TopCat :=
  InducedCategory.hasForget₂ _

instance : CoeSort LightProfinite (Type*) :=
  ⟨fun X => X.toProfinite⟩

@[simp]
lemma forget_ContinuousMap_mk {X Y : LightProfinite} (f : X → Y) (hf : Continuous f) :
    (forget Profinite).map (ContinuousMap.mk f hf) = f :=
  rfl

instance {X : LightProfinite} : TotallyDisconnectedSpace X :=
  X.toProfinite.isTotallyDisconnected

example {X : LightProfinite} : CompactSpace X :=
  inferInstance

example {X : LightProfinite} : T2Space X :=
  inferInstance

@[simp]
theorem coe_id (X : LightProfinite) : (𝟙 ((forget LightProfinite).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget LightProfinite).map f ≫ (forget LightProfinite).map g) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp_apply {X Y Z : LightProfinite} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ x, (f ≫ g) x = g (f x) := by
  intros; rfl

@[simps]
def isoMk {X Y : LightProfinite} (i : X.toProfinite ≅ Y.toProfinite) : X ≅ Y where
  hom := i.hom
  inv := i.inv
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

instance : ReflectsLimits lightToProfinite := inferInstance

instance : ReflectsColimits lightToProfinite := inferInstance

/-- The fully faithful embedding of `LightProfinite` in `TopCat`. -/
@[simps!]
def toTopCat : LightProfinite ⥤ TopCat :=
  lightToProfinite ⋙ Profinite.toTopCat
