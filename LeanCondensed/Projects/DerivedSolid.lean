/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.LightSolid
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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

The definitions using `Functor.totalLeftDerived`/`Functor.totalRightDerived` are conditional on the
corresponding Kan-extension existence typeclasses.  The remaining `sorry`s mark the genuinely
bifunctorial derived constructions which are not yet packaged here.
-/

noncomputable section

open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed

namespace LightCondensed
namespace Solid

attribute [local instance] HasDerivedCategory.standard

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

/-- Placeholder for the bifunctorial derived tensor product on the derived category of solid
abelian groups.

The fixed-variable functors `leftDerivedTensorRight` above are the intended one-variable shadows of
this bifunctor.  A complete construction should either use a bifunctor-derived-functor API or a
suitable K-flat/K-projective replacement theorem. -/
noncomputable def derivedTensor : DSolid ⥤ DSolid ⥤ DSolid := by
  sorry

/-- Placeholder for the expected derived adjunction between derived solidification and the derived
inclusion. -/
noncomputable def derivedSolidificationAdjunction
    [solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))] :
    derivedSolidification ⊣ derivedInclusion := by
  sorry

/-- Placeholder marker for the eventual closed structure: it should relate `derivedTensor` and the
total right-derived internal Hom once the bifunctorial tensor is available. -/
lemma derivedTensor_closed_scaffold : True := by
  trivial

end Solid
end LightCondensed
