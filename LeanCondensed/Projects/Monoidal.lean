/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection

universe u v

noncomputable section

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory
  MonoidalClosed Functor Enriched

attribute [local instance] CategoryTheory.HasForget.instFunLike
  ModuleCat.instMonoidalClosed Sheaf.monoidalCategory

variable (R : Type u) [CommRing R] -- might need some more assumptions

def walkingMulticospanEquivalence {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) :
    WalkingMulticospan (multicospanShapeEnd C) ≌
      WalkingMulticospan (multicospanShapeEnd D) := sorry

instance {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C] :
    EssentiallySmall.{u} (WalkingMulticospan (multicospanShapeEnd C)) where
  equiv_smallCategory :=
    ⟨WalkingMulticospan (multicospanShapeEnd (SmallModel C)), inferInstance,
      ⟨walkingMulticospanEquivalence (equivSmallModel C)⟩⟩

instance {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C] (X : C) :
    EssentiallySmall.{u} (Under X) :=
  sorry

instance : HasLimitsOfShape
    (WalkingMulticospan (multicospanShapeEnd LightProfinite.{u}ᵒᵖ)) (ModuleCat.{u} R) :=
  hasLimitsOfShape_of_essentiallySmall _ _

instance (S : LightProfinite.{u}ᵒᵖ) :
    HasLimitsOfShape (WalkingMulticospan (multicospanShapeEnd (Under S))) (ModuleCat.{u} R) :=
  hasLimitsOfShape_of_essentiallySmall _ _

instance : ((coherentTopology LightProfinite.{u}).W (A := ModuleCat R)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/- This is the monoidal structure on localized categories. -/
instance : MonoidalCategory (LightCondMod.{u} R) := CategoryTheory.Sheaf.monoidalCategory _ _

instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  FunctorCategory.monoidalClosed

/- Constructed using Day's reflection theorem. -/
instance : MonoidalClosed (LightCondMod.{u} R) :=
  haveI : HasWeakSheafify ((coherentTopology LightProfinite.{u})) (ModuleCat R) :=
    inferInstance
  haveI : (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat R)).Monoidal :=
    inferInstance
  haveI : (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Faithful :=
    (fullyFaithfulSheafToPresheaf _ _).faithful
  haveI :  (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Full :=
    (fullyFaithfulSheafToPresheaf _ _).full
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalPreadditive (LightCondMod.{u} R) := sorry

instance : SymmetricCategory (LightCondMod.{u} R) := sorry
