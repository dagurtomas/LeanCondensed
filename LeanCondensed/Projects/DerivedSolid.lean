/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.SolidProjectiveGenerator
import LeanCondensed.Mathlib.Algebra.Homology.DerivedCategory.TwoVariable
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Generator.Preadditive

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

The scaffold keeps the remaining mathematical obligations as explicit declarations with `sorry`,
rather than hiding them as assumptions on downstream definitions.  In particular, existence of the
relevant total derived functors, K-flat tensor data, and the derived solidification adjunction are
all named below.
-/

noncomputable section

universe w v u

open CategoryTheory Functor Limits LightCondensed MonoidalCategory MonoidalClosed

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A projective separator gives enough projectives.  The coproduct is indexed by `Shrink (G ⟶ X)`
so that this applies in locally small categories whose hom types are not themselves small enough for
available coproducts. -/
lemma enoughProjectives_of_projective_separator_shrink {C : Type u} [Category.{v} C]
    [LocallySmall.{w} C] (G : C) [Projective G] (hG : IsSeparator G)
    [∀ X : C, HasCoproduct (fun _ : Shrink (G ⟶ X) => G)] : EnoughProjectives C := by
  refine ⟨fun X => ⟨{
    p := ∐ fun _ : Shrink (G ⟶ X) => G,
    projective := by
      constructor
      intro E Y f e he
      letI : Epi e := he
      refine ⟨Sigma.desc fun i : Shrink (G ⟶ X) =>
        Projective.factorThru (Sigma.ι (fun _ : Shrink (G ⟶ X) => G) i ≫ f) e, ?_⟩
      apply colimit.hom_ext
      intro i
      simp
    f := Sigma.desc fun i : Shrink (G ⟶ X) => (equivShrink (G ⟶ X)).symm i,
    epi := by
      constructor
      intro Y u v huv
      refine hG.def u v ?_
      intro h
      have hh := congrArg (fun e => Sigma.ι (fun _ : Shrink (G ⟶ X) => G)
        (equivShrink (G ⟶ X) h) ≫ e) huv
      simpa [Category.assoc] using hh }⟩⟩

end CategoryTheory

namespace LightCondensed
namespace Solid

attribute [local instance] HasDerivedCategory.standard

instance (X : Solid) : PreservesColimits (tensorRight X) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

instance (X : Solid) : (tensorLeft X).Additive :=
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
  additive_of_preservesBinaryBiproducts _

instance (X : Solid) : (tensorRight X).Additive :=
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
  additive_of_preservesBinaryBiproducts _

instance : MonoidalPreadditive Solid where
  whiskerLeft_zero {X Y Z} := Functor.map_zero (tensorLeft X) Y Z
  zero_whiskerRight {X Y Z} := Functor.map_zero (tensorRight X) Y Z
  whiskerLeft_add {X Y Z} f g := by
    change (tensorLeft X).map (f + g) = (tensorLeft X).map f + (tensorLeft X).map g
    simpa using (map_add (F := tensorLeft X) (f := f) (g := g))
  add_whiskerRight {X Y Z} f g := by
    change (tensorRight X).map (f + g) = (tensorRight X).map f + (tensorRight X).map g
    simpa using (map_add (F := tensorRight X) (f := f) (g := g))

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

/-- Obligation: degreewise solidification followed by localization admits a total left-derived
functor.  This should follow from the general existence theorem for total left-derived functors once
the relevant size/existence hypotheses are available. -/
instance solidificationToDerived_hasLeftDerivedFunctor :
    solidificationToDerived.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) := by
  sorry

/-- The left-derived solidification functor. -/
noncomputable abbrev derivedSolidification : DLightCondAb ⥤ DSolid :=
  solidificationToDerived.totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- The comparison map characterizing `derivedSolidification` as a total left-derived functor. -/
noncomputable abbrev derivedSolidificationCounit :
    DerivedCategory.Q ⋙ derivedSolidification ⟶ solidificationToDerived :=
  solidificationToDerived.totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))

/-- The inclusion of solid abelian groups, applied degreewise to cochain complexes. -/
noncomputable abbrev inclusionComplexes :
    CochainComplex Solid ℤ ⥤ CochainComplex LightCondAb ℤ :=
  isSolid.ι.mapHomologicalComplex (ComplexShape.up ℤ)

/-- Obligation: the solidification adjunction lifts degreewise to cochain complexes. -/
noncomputable def solidificationComplexesAdjunction :
    solidificationComplexes ⊣ inclusionComplexes := by
  sorry

/-- The exact functor on derived categories induced by the inclusion `Solid ⥤ LightCondAb`. -/
noncomputable abbrev derivedInclusion : DSolid ⥤ DLightCondAb :=
  isSolid.ι.mapDerivedCategory

/-- The inclusion-derived functor is induced by applying the inclusion degreewise to complexes. -/
noncomputable abbrev derivedInclusionFactors :
    DerivedCategory.Q ⋙ derivedInclusion ≅ inclusionComplexes ⋙ DerivedCategory.Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The comparison map exhibiting `derivedInclusion` as a right-derived functor of the degreewise
inclusion. -/
noncomputable abbrev derivedInclusionComparison :
    inclusionComplexes ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derivedInclusion :=
  derivedInclusionFactors.inv

/-- The exact derived inclusion is the right-derived functor of the degreewise inclusion. -/
instance derivedInclusion_isRightDerivedFunctor :
    derivedInclusion.IsRightDerivedFunctor derivedInclusionComparison
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) derivedInclusion derivedInclusionFactors

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

/-- Obligation: right tensoring by a fixed solid object admits a total left-derived functor. -/
instance tensorRightToDerived_hasLeftDerivedFunctor (A : Solid) :
    (tensorRightToDerived A).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) := by
  sorry

/-- The left-derived functor of right tensoring by a fixed solid object. -/
noncomputable abbrev leftDerivedTensorRight (A : Solid) : DSolid ⥤ DSolid :=
  (tensorRightToDerived A).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The comparison map characterizing `leftDerivedTensorRight A`. -/
noncomputable abbrev leftDerivedTensorRightCounit (A : Solid) :
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

/-- Obligation: internal Hom out of a fixed solid object admits a total right-derived functor. -/
instance ihomToDerived_hasRightDerivedFunctor (A : Solid) :
    (ihomToDerived A).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) := by
  sorry

/-- The right-derived functor of internal Hom out of a fixed solid object. -/
noncomputable abbrev rightDerivedIhom (A : Solid) : DSolid ⥤ DSolid :=
  (ihomToDerived A).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The comparison map characterizing `rightDerivedIhom A`. -/
noncomputable abbrev rightDerivedIhomUnit (A : Solid) :
    ihomToDerived A ⟶ DerivedCategory.Q ⋙ rightDerivedIhom A :=
  (ihomToDerived A).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))

/-- The unit object for the eventual derived tensor product on `DSolid`. -/
noncomputable abbrev derivedTensorUnit : DSolid :=
  (DerivedCategory.singleFunctor Solid 0).obj (𝟙_ Solid)

open CategoryTheory.DerivedCategory.TwoVariable

/-- Solid abelian groups have enough projective objects, using the explicit projective generator. -/
instance solid_enoughProjectives : EnoughProjectives Solid :=
  enoughProjectives_of_projective_separator_shrink solidProjectiveGenerator
    solidProjectiveGenerator_isSeparator

/-- Solid abelian groups have enough K-projective complex resolutions, once they have enough
projective objects. -/
lemma solid_hasEnoughKProjectives : HasEnoughKProjectives Solid :=
  hasEnoughKProjectives_of_enoughProjectives Solid

/-- Obligation: K-projective complexes of solid abelian groups are K-flat for the solid tensor
product. -/
lemma solid_kProjective_isKFlat (K : CochainComplex Solid ℤ) (hK : CochainComplex.IsKProjective K) :
    IsKFlat K := by
  sorry

/-- K-flat solid complexes compute the derived category of solid abelian groups, once enough
K-projectives are available and K-projective complexes are known to be K-flat. -/
lemma solid_hasEnoughKFlats : HasEnoughKFlats Solid :=
  hasEnoughKFlats_of_hasEnoughKProjectives Solid solid_hasEnoughKProjectives
    solid_kProjective_isKFlat

/-- Tensoring K-flat solid complexes sends K-flat quasi-isomorphisms in both variables to
quasi-isomorphisms. -/
lemma solidTensorComplex_inverts_kflat : InvertsKFlatQuasiIso₂ solidTensorComplex :=
  curriedTensor_invertsKFlatQuasiIso₂ Solid

/-- The bifunctorial derived tensor product on the derived category of solid abelian groups,
computed from K-flat replacements. -/
noncomputable def derivedTensor : DSolid ⥤ DSolid ⥤ DSolid :=
  leftDerived₂ByKFlatsCurried solidTensorComplex solidTensorComplex_inverts_kflat
    solid_hasEnoughKFlats solid_hasEnoughKFlats

/-- Obligation: the composite `derivedSolidification ⋙ derivedInclusion` is the left-derived
composite needed by `Adjunction.derived`.  This is the absoluteness input in the general derived
adjunction theorem. -/
instance derivedSolidification_comp_derivedInclusion_isLeftDerivedFunctor :
    (derivedSolidification ⋙ derivedInclusion).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight derivedSolidificationCounit derivedInclusion)
      (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)) := by
  sorry

/-- Obligation: the composite `derivedInclusion ⋙ derivedSolidification` is the right-derived
composite needed by `Adjunction.derived`.  This is the dual absoluteness input in the general
derived adjunction theorem. -/
instance derivedInclusion_comp_derivedSolidification_isRightDerivedFunctor :
    (derivedInclusion ⋙ derivedSolidification).IsRightDerivedFunctor
      (Functor.whiskerRight derivedInclusionComparison derivedSolidification ≫
        (Functor.associator _ _ _).hom)
      (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ)) := by
  sorry

/-- The derived adjunction between derived solidification and the derived inclusion, obtained from
`Adjunction.derived` once the explicit derived-functor obligations above are discharged. -/
noncomputable def derivedSolidificationAdjunction : derivedSolidification ⊣ derivedInclusion :=
  solidificationComplexesAdjunction.derived
    (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso Solid (ComplexShape.up ℤ))
    derivedSolidificationCounit
    derivedInclusionComparison

/-- Placeholder marker for the eventual closed structure: it should relate `derivedTensor` and the
total right-derived internal Hom once the bifunctorial tensor is available. -/
lemma derivedTensor_closed_scaffold : True := by
  trivial

end Solid
end LightCondensed
