/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.LightSolid
import LeanCondensed.Mathlib.Algebra.Homology.DerivedCategory.TwoVariable
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Scaffold for derived light solid abelian groups

This file records the intended derived-category interfaces around light solid abelian groups:

* the derived category of `LightCondAb` and of `Solid`;
* the left-derived solidification functor;
* the exact derived inclusion of solid objects into light condensed abelian groups;
* fixed-variable left-derived tensor functors and right-derived internal Homs;
* placeholders for the eventual bifunctorial derived tensor product and derived adjunctions.

The general two-variable localization scaffold is in
`LeanCondensed.Mathlib.Algebra.Homology.DerivedCategory.TwoVariable`.

The definitions using `Functor.totalLeftDerived`/`Functor.totalRightDerived` are conditional on the
corresponding Kan-extension existence typeclasses. The bifunctorial tensor product is similarly
conditional on an adapted replacement package, e.g. K-flat replacements once available for `Solid`.
-/

noncomputable section

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed

namespace LightCondensed
namespace Solid

attribute [local instance] HasDerivedCategory.standard

instance (X : Solid) : PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

instance (X : Solid) : (tensorLeft X).Additive := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance (X : Solid) : (tensorRight X).Additive := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance : MonoidalPreadditive Solid where
  whiskerLeft_zero {X Y Z} := by
    change (tensorLeft X).map (0 : Y ⟶ Z) = 0
    exact Functor.map_zero (tensorLeft X) Y Z
  zero_whiskerRight {X Y Z} := by
    change (tensorRight X).map (0 : Y ⟶ Z) = 0
    exact Functor.map_zero (tensorRight X) Y Z
  whiskerLeft_add {X Y Z} f g := by
    change (tensorLeft X).map (f + g) = (tensorLeft X).map f + (tensorLeft X).map g
    simpa using (Functor.map_add (F := tensorLeft X) (f := f) (g := g))
  add_whiskerRight {X Y Z} f g := by
    change (tensorRight X).map (f + g) = (tensorRight X).map f + (tensorRight X).map g
    simpa using (Functor.map_add (F := tensorRight X) (f := f) (g := g))

/-- The derived category of light condensed abelian groups. -/
abbrev DLightCondAb := DerivedCategory LightCondAb

/-- The derived category of light solid abelian groups. -/
abbrev DSolid := DerivedCategory Solid

/-- Solidification applied degreewise to cochain complexes. -/
noncomputable abbrev solidificationComplexes :
    CochainComplex LightCondAb ℤ ⥤ CochainComplex Solid ℤ :=
  solidification.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise solidification followed by localization to the derived category of solid objects. -/
noncomputable abbrev solidificationToDerived :
    CochainComplex LightCondAb ℤ ⥤ DSolid :=
  solidificationComplexes ⋙ DerivedCategory.Q

/-- The left-derived solidification functor, when the corresponding total left-derived functor
exists. -/
noncomputable abbrev derivedSolidification
    [solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))] :
    DLightCondAb ⥤ DSolid :=
  solidificationToDerived.totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- The comparison map characterizing `derivedSolidification` as a total left-derived functor. -/
noncomputable abbrev derivedSolidificationCounit
    [solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))] :
    DerivedCategory.Q ⋙ derivedSolidification ⟶ solidificationToDerived :=
  solidificationToDerived.totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- If solidification is later shown to preserve finite limits, the left-derived construction above
agrees with the derived functor induced by the exact functor `solidification`. -/
noncomputable abbrev exactDerivedSolidification [PreservesFiniteLimits solidification] :
    DLightCondAb ⥤ DSolid :=
  solidification.mapDerivedCategory

/-- The exact-derived solidification functor is induced by applying solidification degreewise to
complexes. -/
noncomputable abbrev exactDerivedSolidificationFactors [PreservesFiniteLimits solidification] :
    DerivedCategory.Q ⋙ exactDerivedSolidification ≅
      solidification.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  solidification.mapDerivedCategoryFactors

/-- The exact functor on derived categories induced by the inclusion `Solid ⥤ LightCondAb`. -/
noncomputable abbrev derivedInclusion : DSolid ⥤ DLightCondAb :=
  isSolid.ι.mapDerivedCategory

/-- The inclusion-derived functor is induced by applying the inclusion degreewise to complexes. -/
noncomputable abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅
      isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The tensor product bifunctor on cochain complexes of solid abelian groups. -/
noncomputable abbrev solidTensorComplex :
    CochainComplex Solid ℤ ⥤ CochainComplex Solid ℤ ⥤ CochainComplex Solid ℤ :=
  curriedTensor (CochainComplex Solid ℤ)

/-- Tensoring on the right by a solid object, applied degreewise to cochain complexes. -/
noncomputable abbrev tensorRightComplexes (A : Solid) :
    CochainComplex Solid ℤ ⥤ CochainComplex Solid ℤ :=
  (tensorRight A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise right tensoring by a solid object, followed by localization. -/
noncomputable abbrev tensorRightToDerived (A : Solid) :
    CochainComplex Solid ℤ ⥤ DSolid :=
  tensorRightComplexes A ⋙ DerivedCategory.Q

/-- The left-derived functor of right tensoring by a fixed solid object. -/
noncomputable abbrev leftDerivedTensorRight (A : Solid)
    [(tensorRightToDerived A).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))] :
    DSolid ⥤ DSolid :=
  (tensorRightToDerived A).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The comparison map characterizing `leftDerivedTensorRight A`. -/
noncomputable abbrev leftDerivedTensorRightCounit (A : Solid)
    [(tensorRightToDerived A).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))] :
    DerivedCategory.Q ⋙ leftDerivedTensorRight A ⟶ tensorRightToDerived A :=
  (tensorRightToDerived A).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- Internal Hom out of a fixed solid object, applied degreewise to cochain complexes. -/
noncomputable abbrev ihomComplexes (A : Solid) :
    CochainComplex Solid ℤ ⥤ CochainComplex Solid ℤ :=
  (ihom A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise internal Hom out of a fixed solid object, followed by localization. -/
noncomputable abbrev ihomToDerived (A : Solid) :
    CochainComplex Solid ℤ ⥤ DSolid :=
  ihomComplexes A ⋙ DerivedCategory.Q

/-- The right-derived functor of internal Hom out of a fixed solid object. -/
noncomputable abbrev rightDerivedIhom (A : Solid)
    [(ihomToDerived A).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))] :
    DSolid ⥤ DSolid :=
  (ihomToDerived A).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The comparison map characterizing `rightDerivedIhom A`. -/
noncomputable abbrev rightDerivedIhomUnit (A : Solid)
    [(ihomToDerived A).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))] :
    ihomToDerived A ⟶ DerivedCategory.Q ⋙ rightDerivedIhom A :=
  (ihomToDerived A).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The unit object for the eventual derived tensor product on `DSolid`. -/
noncomputable abbrev derivedTensorUnit : DSolid :=
  (DerivedCategory.singleFunctor Solid 0).obj (𝟙_ Solid)

open CategoryTheory.DerivedCategory.TwoVariable

/-- Adapted replacement data for constructing the derived tensor product of solid abelian groups.

The intended instance should use K-flat complexes: the adapted classes should be K-flat solid
complexes, the `inverts` field says that the complex-level tensor sends quasi-isomorphisms between
adapted complexes to quasi-isomorphisms, and the localized-equivalence fields say that adapted
complexes compute the derived category. -/
abbrev HasTensorAdapted : Type _ := HasAdaptedDerived₂ solidTensorComplex

/-- The bifunctorial derived tensor product on the derived category of solid abelian groups,
computed from an adapted replacement class such as K-flat complexes. -/
noncomputable def derivedTensor [HasTensorAdapted] : DSolid ⥤ DSolid ⥤ DSolid :=
  derived₂CurriedOfAdapted solidTensorComplex

/-- Data witnessing the expected derived adjunction between derived solidification and the derived
inclusion.

A future proof should construct this from the general derived-adjunction API, by showing that the
left-derived solidification is absolute enough to compose with the exact derived inclusion. -/
class HasDerivedSolidificationAdjunction
    [solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))] where
  adjunction : derivedSolidification ⊣ derivedInclusion

/-- The expected derived adjunction between derived solidification and the derived inclusion,
once the relevant absolute-derived-functor compatibility has been supplied. -/
noncomputable def derivedSolidificationAdjunction
    [solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))]
    [h : HasDerivedSolidificationAdjunction] :
    derivedSolidification ⊣ derivedInclusion :=
  h.adjunction

/-- Placeholder marker for the eventual closed structure: it should relate `derivedTensor` and the
total right-derived internal Hom once the bifunctorial tensor is available. -/
lemma derivedTensor_closed_scaffold : True := by
  trivial

end Solid
end LightCondensed
