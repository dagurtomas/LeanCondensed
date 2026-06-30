/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.LightSolid
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Generator.Basic

/-!
# The projective generator of solid abelian groups

This file isolates the categorical shell for the proof that the countable product of copies of
`ℤ` is a projective generator of `Solid`.  The hard analytic/derived inputs from the proof are kept
as explicit named obligations:

* `solidPIsoProduct`, identifying `solidification.obj (P ℤ)` with the countable product of `ℤ`;
* `solidifiedFreeRetractSolidPInfinite`, the infinite-test-object shift-retract calculation.

The remaining declarations are formal category-theory consequences of these named inputs, together
with the ordinary projectivity of `P ℤ`, the separation statement for solidified free
representables, and the finite-coproduct reduction proved below.
-/

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint

namespace CategoryTheory

/-- Separators are invariant under isomorphism. -/
lemma isSeparator_of_iso {C : Type*} [Category C]
    {G H : C} (e : G ≅ H) (hG : IsSeparator G) :
    IsSeparator H := by
  rw [isSeparator_def] at hG ⊢
  exact fun _ _ f g hH ↦ hG f g fun k ↦ by simpa using e.hom ≫= hH (e.inv ≫ k)

/-- If a jointly separating family consists of retracts of `G`, then `G` is a separator. -/
lemma isSeparator_of_retracts_of_hom_ext {C : Type*} [Category C] {I : Type*} (F : I → C) (G : C)
    (hjoint : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i (k : F i ⟶ X), k ≫ f = k ≫ g) → f = g)
    (r : ∀ i, Retract (F i) G) : IsSeparator G := by
  rw [isSeparator_def]
  exact fun _ _ f g hG ↦ hjoint f g fun i k ↦ by simpa using (r i).i ≫= hG ((r i).r ≫ k)

/-- If a functor preserves a binary coproduct and the target has zero morphisms, the image of the
first summand is a retract of the image of the coproduct. -/
noncomputable def functor_obj_retract_coprod
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) (X Y : C) [HasBinaryCoproduct X Y] [HasBinaryCoproduct (F.obj X) (F.obj Y)]
    [PreservesColimit (pair X Y) F] : Retract (F.obj X) (F.obj (X ⨿ Y)) where
  i := F.map (coprod.inl : X ⟶ X ⨿ Y)
  r := inv (coprodComparison F X Y) ≫ coprod.desc (𝟙 (F.obj X)) 0
  retract := by rw [map_inl_inv_coprodComparison_assoc, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
/-- If the tensor unit is projective, internal projectivity implies ordinary projectivity.
This packages the standard adjunction argument: maps out of `P` are global sections of
`P ⟶[C] -`, and `P ⟶[C] -` preserves epimorphisms by internal projectivity. -/
lemma projective_of_internallyProjective_of_projective_unit
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    (P : C) [Projective (𝟙_ C)] [InternallyProjective P] : Projective P where
  factors {E X} f e he := by
    obtain ⟨g', hg'⟩ := Projective.factors (MonoidalClosed.curry ((ρ_ P).hom ≫ f)) ((ihom P).map e)
    refine ⟨(ρ_ P).inv ≫ MonoidalClosed.uncurry g', ?_⟩
    simpa [MonoidalClosed.uncurry_natural_right] using (ρ_ P).inv ≫=
      (congrArg MonoidalClosed.uncurry hg')

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Abstract data for the shift-retract diagram used in the projective-generator proof. -/
structure ShiftRetractData (L : C ⥤ D) where
  xObj : C
  aObj : C
  bObj : C
  s : xObj ⟶ xObj
  toB : xObj ⟶ bObj
  toA : xObj ⟶ aObj
  g : aObj ⟶ bObj
  comm : s ≫ toB = toA ≫ g
  sect : bObj ⟶ xObj
  sect_fac : sect ≫ toB = 𝟙 bObj
  inverted : IsIso (L.map s)

namespace ShiftRetractData

/-- The formal retract extracted from a shift-retract square after applying a functor that inverts
its left vertical map. -/
noncomputable def retract {L : C ⥤ D}
    (d : ShiftRetractData L) : Retract (L.obj d.bObj) (L.obj d.aObj) := by
  letI := d.inverted
  refine {
    i := L.map d.sect ≫ inv (L.map d.s) ≫ L.map d.toA
    r := L.map d.g
    retract := ?_ }
  have hcomm : L.map d.s ≫ L.map d.toB = L.map d.toA ≫ L.map d.g := by
    simpa only [Functor.map_comp] using congrArg (fun f => L.map f) d.comm
  calc
    (L.map d.sect ≫ inv (L.map d.s) ≫ L.map d.toA) ≫ L.map d.g
        = L.map d.sect ≫ inv (L.map d.s) ≫ (L.map d.toA ≫ L.map d.g) := by
          simp [Category.assoc]
    _ = L.map d.sect ≫ inv (L.map d.s) ≫ (L.map d.s ≫ L.map d.toB) := by
          rw [← hcomm]
    _ = L.map d.sect ≫ L.map d.toB := by
          simp
    _ = L.map (d.sect ≫ d.toB) := by
          rw [Functor.map_comp]
    _ = 𝟙 (L.obj d.bObj) := by
          rw [d.sect_fac, Functor.map_id]

/-- If the complementary idempotent extracted from a shift-retract diagram is the identity, then
`L.map d.g` is an isomorphism. -/
lemma isIso_map_g {L : C ⥤ D}
    (d : ShiftRetractData L)
    (hidempotent : L.map d.g ≫ (d.retract).i = 𝟙 (L.obj d.aObj)) :
    IsIso (L.map d.g) := by
  letI := d.inverted
  exact ⟨(d.retract).i, hidempotent, d.retract.retract⟩

end ShiftRetractData

end CategoryTheory

namespace LightProfinite

/-- A surjection of light profinite spaces onto a finite target admits a section. -/
lemma exists_section_of_epi_to_finite {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] : ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y := by
  have hf : Function.Surjective f := (LightProfinite.epi_iff_surjective f).mp inferInstance
  let sFun : Y → X := fun y => (hf y).choose
  have hsFun : ∀ y, f (sFun y) = y := fun y => (hf y).choose_spec
  letI : DiscreteTopology Y := Finite.instDiscreteTopology
  let s : Y ⟶ X := ConcreteCategory.ofHom ⟨sFun, continuous_of_discreteTopology⟩
  refine ⟨s, ?_⟩
  ext y
  exact hsFun y

/-- A chosen section of a surjection of light profinite spaces onto a finite target. -/
noncomputable def sectionOfEpiToFinite {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] : Y ⟶ X :=
  (exists_section_of_epi_to_finite f).choose

@[simp]
lemma sectionOfEpiToFinite_comp {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] :
    sectionOfEpiToFinite f ≫ f = 𝟙 Y :=
  (exists_section_of_epi_to_finite f).choose_spec

/-- The finite stages in the standard inverse-limit presentation are finite. -/
instance finite_component (T : LightProfinite) (n : ℕ) : Finite (T.component n) :=
  inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj (T.fintypeDiagram.obj ⟨n⟩)))

/-- A chosen section of the projection from a light profinite set to a finite stage. -/
noncomputable def projSection (T : LightProfinite) (n : ℕ) : T.component n ⟶ T := by
  haveI : Epi (T.proj n) :=
    (LightProfinite.epi_iff_surjective _).mpr (T.proj_surjective n)
  exact sectionOfEpiToFinite (T.proj n)

@[simp]
lemma projSection_proj (T : LightProfinite) (n : ℕ) :
    projSection T n ≫ T.proj n = 𝟙 (T.component n) := by
  dsimp [projSection]
  haveI : Epi (T.proj n) :=
    (LightProfinite.epi_iff_surjective _).mpr (T.proj_surjective n)
  exact sectionOfEpiToFinite_comp (T.proj n)

/-- A section of the `n`th projection has the expected projection to every earlier finite stage. -/
lemma projSection_proj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    projSection T n ≫ T.proj k = T.transitionMapLE h := by
  rw [← T.proj_comp_transitionMapLE h]
  rw [← Category.assoc, projSection_proj]
  simp

/-- The finite-rank endomorphism of `T` obtained by projecting to the `n`th finite quotient and
returning along the chosen section. -/
noncomputable def finiteApproxRetraction (T : LightProfinite) (n : ℕ) : T ⟶ T :=
  T.proj n ≫ projSection T n

@[simp]
lemma finiteApproxRetraction_proj (T : LightProfinite) (n : ℕ) :
    finiteApproxRetraction T n ≫ T.proj n = T.proj n := by
  simp [finiteApproxRetraction, Category.assoc]

/-- The finite-rank retraction agrees with the identity on all finite stages up to `n`. -/
lemma finiteApproxRetraction_proj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    finiteApproxRetraction T n ≫ T.proj k = T.proj k := by
  calc
    finiteApproxRetraction T n ≫ T.proj k
        = T.proj n ≫ (projSection T n ≫ T.proj k) := by
          rw [finiteApproxRetraction, Category.assoc]
    _ = T.proj n ≫ T.transitionMapLE h := by
          rw [projSection_proj_le]
    _ = T.proj k := T.proj_comp_transitionMapLE h

/-- A locally constant function on a light profinite space factors through one of the finite stages
in the chosen sequential presentation. -/
lemma exists_locallyConstant_factor_proj (T : LightProfinite) {α : Type*}
    (f : LocallyConstant T α) :
    ∃ k : ℕ, ∃ g : LocallyConstant (T.component k) α,
      f = g.comap (T.proj k).hom.hom := by
  have hlim : IsLimit (lightToProfinite.mapCone T.asLimitCone) :=
    isLimitOfPreserves lightToProfinite T.asLimit
  obtain ⟨j, g, hg⟩ := Profinite.exists_locallyConstant
    (C := lightToProfinite.mapCone T.asLimitCone) hlim f
  exact ⟨j.unop, g, hg⟩

end LightProfinite

namespace LightCondensed
namespace Solid

/-- The solid abelian group `ℤ`. -/
noncomputable abbrev solidInteger : Solid :=
  ⟨(LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ), isSolid_int⟩

/-- The intended projective generator of solid abelian groups: a countable product of copies of
`ℤ`. -/
noncomputable abbrev solidProjectiveGenerator : Solid :=
  ∏ᶜ fun _ : ℕ => solidInteger

namespace ProjectiveGeneratorProof

/-- The discrete light condensed abelian group `ℤ`. -/
abbrev Zdisc : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

-- Sections of the discrete light condensed abelian group `ℤ` are locally constant integer-valued
-- functions.
set_option backward.isDefEq.respectTransparency false in
noncomputable def zdiscSectionsEquiv (S : LightProfinite) :
    Zdisc.obj.obj ⟨S⟩ ≃ LocallyConstant S ℤ where
  toFun x := by
    let y := ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app
      (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩ x
    change LocallyConstant S ℤ at y
    exact y
  invFun y := by
    let x : ((LightCondMod.LocallyConstant.functor ℤ).obj (ModuleCat.of ℤ ℤ)).obj.obj ⟨S⟩ := y
    exact ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).hom.app
      (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩ x
  left_inv x := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)
    change (e.inv ≫ e.hom).hom.app ⟨S⟩ x = x
    rw [Iso.inv_hom_id]
    rfl
  right_inv y := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)
    change (e.hom ≫ e.inv).hom.app ⟨S⟩ y = y
    rw [Iso.hom_inv_id]
    rfl

/-- The locally constant-function description of `ℤ`-sections is natural in the test object. -/
lemma zdiscSectionsEquiv_map {S S' : LightProfinite} (φ : S' ⟶ S)
    (x : Zdisc.obj.obj ⟨S⟩) :
    zdiscSectionsEquiv S' (Zdisc.obj.map φ.op x) =
      (zdiscSectionsEquiv S x).comap φ.hom.hom := by
  dsimp [zdiscSectionsEquiv]
  exact LightCondMod.hom_naturality_apply ℤ
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)) φ.op x

@[simp]
lemma zdiscSectionsEquiv_zero (S : LightProfinite) :
    zdiscSectionsEquiv S (0 : Zdisc.obj.obj ⟨S⟩) = 0 := by
  dsimp [zdiscSectionsEquiv]
  simp
  rfl

/-- The solidification of the sequence object `P ℤ`. -/
noncomputable abbrev solidP : Solid :=
  solidification.obj (P ℤ)

/-- The countable product of copies of `ℤ` in `Solid`. -/
noncomputable abbrev productInt : Solid :=
  solidProjectiveGenerator

/-- Maps out of a free light condensed abelian group are the corresponding point values. -/
noncomputable def freeHomEquivPoints (T : LightProfinite) (A : LightCondAb) :
    ((free ℤ).obj T.toCondensed ⟶ A) ≃ A.obj.obj ⟨T⟩ :=
  ((freeForgetAdjunction ℤ).homEquiv T.toCondensed A).trans
    (coherentTopology LightProfinite).yonedaEquiv

lemma freeHomEquivPoints_map {T T' : LightProfinite} (φ : T' ⟶ T)
    (A : LightCondAb) (f : (free ℤ).obj T.toCondensed ⟶ A) :
    freeHomEquivPoints T' A (((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫ f) =
      A.obj.map φ.op (freeHomEquivPoints T A f) := by
  dsimp [freeHomEquivPoints]
  erw [Adjunction.homEquiv_naturality_left]
  exact (GrothendieckTopology.yonedaEquiv_naturality (coherentTopology LightProfinite)
    (((freeForgetAdjunction ℤ).homEquiv T.toCondensed A) f) φ).symm

lemma freeHomEquivPoints_symm_map {T T' : LightProfinite} (φ : T' ⟶ T)
    (A : LightCondAb) (x : A.obj.obj ⟨T⟩) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫
      (freeHomEquivPoints T A).symm x =
      (freeHomEquivPoints T' A).symm (A.obj.map φ.op x) := by
  apply (freeHomEquivPoints T' A).injective
  rw [freeHomEquivPoints_map]
  simp

/-- The point-value description of maps out of a free object is natural in the target. -/
lemma freeHomEquivPoints_comp (T : LightProfinite) {A B : LightCondAb}
    (f : (free ℤ).obj T.toCondensed ⟶ A) (φ : A ⟶ B) :
    freeHomEquivPoints T B (f ≫ φ) =
      φ.hom.app ⟨T⟩ (freeHomEquivPoints T A f) := by
  dsimp [freeHomEquivPoints]
  erw [Adjunction.homEquiv_naturality_right]
  erw [GrothendieckTopology.yonedaEquiv_comp]

@[simp]
lemma freeHomEquivPoints_zero (T : LightProfinite) (A : LightCondAb) :
    freeHomEquivPoints T A (0 : (free ℤ).obj T.toCondensed ⟶ A) = 0 := by
  have h := freeHomEquivPoints_comp T (𝟙 ((free ℤ).obj T.toCondensed))
    (0 : (free ℤ).obj T.toCondensed ⟶ A)
  simpa using h

/-- The free light condensed abelian group on the point is the tensor unit. -/
noncomputable def freePointIsoUnit :
    (LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ≅ 𝟙_ LightCondAb :=
  (LightCondensed.free ℤ).mapIso (Functor.Monoidal.εIso lightProfiniteToLightCondSet).symm ≪≫
    (Functor.Monoidal.εIso (LightCondensed.free ℤ)).symm

/-- The free light condensed abelian group on the point is projective: local lifts over a cover of
`*` can be pulled back along any chosen point of the cover. -/
instance freePoint_projective :
    Projective ((LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) where
  factors {A B} f e he := by
    letI : Epi e := he
    let pt : LightProfinite := LightProfinite.of PUnit.{1}
    obtain ⟨T, π, g, hπ, hg⟩ :=
      LightCondMod.factorsThru_lightProfinite_epi_of_epi ℤ e (S := pt) f
    have hπsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp hπ
    obtain ⟨t, ht⟩ := hπsurj PUnit.unit
    let σ : pt ⟶ T := ConcreteCategory.ofHom ⟨fun _ => t, continuous_const⟩
    have hσπ : σ ≫ π = 𝟙 pt := by
      ext x
    refine ⟨(LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map σ) ≫ g, ?_⟩
    simp only [Category.assoc]
    rw [← hg]
    change (LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map σ) ≫
        ((LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map π) ≫ f) = f
    rw [← Category.assoc]
    simp [← Functor.map_comp, hσπ]

/-- The tensor unit of light condensed abelian groups is projective. -/
instance tensorUnit_projective : Projective (𝟙_ LightCondAb) :=
  Projective.of_iso freePointIsoUnit freePoint_projective

/-- The object `P ℤ` is projective in light condensed abelian groups. -/
instance projective_P : Projective (P ℤ) := by
  haveI : Projective (𝟙_ LightCondAb) := tensorUnit_projective
  exact CategoryTheory.projective_of_internallyProjective_of_projective_unit (P ℤ)

/-- Solidification preserves projective objects because its right adjoint, the inclusion of solid
objects, preserves epimorphisms. -/
instance solidification_preservesProjectiveObjects :
    solidification.PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    solidificationAdjunction

/-- The solidification of `P ℤ` is projective in `Solid`. -/
instance projective_solidP : Projective solidP := by
  dsimp [solidP]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary currying intertwines external precomposition with internal precomposition. -/
lemma curry'_pre_app {X Y Z : LightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MonoidalClosed.curry' (f ≫ g) =
      MonoidalClosed.curry' g ≫ (MonoidalClosed.pre f).app Z := by
  dsimp [MonoidalClosed.curry']
  rw [MonoidalClosed.curry_pre_app]
  congr 1
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The defining map `1 - shift : P ℤ ⟶ P ℤ` is local for the solidification localization. -/
lemma oneMinusShift_mem_isLocal : isSolid.isLocal (oneMinusShift ℤ) := by
  intro Z hZ
  dsimp [isSolid] at hZ
  let φ := ((MonoidalClosed.pre (oneMinusShift ℤ)).app Z)
  haveI : IsIso φ := hZ
  have hcompat : ∀ g : P ℤ ⟶ Z,
      MonoidalClosed.curry' ((oneMinusShift ℤ) ≫ g) = MonoidalClosed.curry' g ≫ φ := by
    intro g
    exact curry'_pre_app (oneMinusShift ℤ) g
  constructor
  · intro g₁ g₂ h
    apply MonoidalClosed.curry'_injective
    apply (cancel_mono φ).1
    rw [← hcompat, ← hcompat]
    exact congrArg MonoidalClosed.curry' h
  · intro g
    let a : 𝟙_ LightCondAb ⟶ (ihom (P ℤ)).obj Z := MonoidalClosed.curry' g ≫ inv φ
    refine ⟨MonoidalClosed.uncurry' a, ?_⟩
    apply MonoidalClosed.curry'_injective
    rw [hcompat]
    dsimp [a, φ]
    simp

/-- Tensoring `1 - shift` on the right is inverted by solidification. -/
lemma solidification_map_oneMinusShift_tensor_isIso (M : LightCondAb) :
    IsIso (solidification.map ((oneMinusShift ℤ) ▷ M)) := by
  apply Localization.inverts solidification isSolid.isLocal
  exact isSolid.isLocal.whiskerRight_mem (oneMinusShift ℤ) oneMinusShift_mem_isLocal M

/-- Obligation: the solidification of `P ℤ` is the countable product of copies of `ℤ`.  This is the
heart-level form of the paper's bounded-sequence and derived-solidification calculation. -/
noncomputable def solidPIsoProduct : solidP ≅ productInt := by
  sorry

/-- Homs from solidified free representables are their values on the representing test object. -/
noncomputable def solidifiedFreeHomEquiv
    (T : LightProfinite) (A : Solid) :
    (solidification.obj ((free ℤ).obj T.toCondensed) ⟶ A) ≃ A.1.obj.obj ⟨T⟩ :=
  (solidificationAdjunction.homEquiv ((free ℤ).obj T.toCondensed) A).trans
    (((LightCondensed.freeForgetAdjunction ℤ).homEquiv T.toCondensed (isSolid.ι.obj A)).trans
      (coherentTopology LightProfinite).yonedaEquiv)

lemma solidifiedFreeHomEquiv_comp
    (T : LightProfinite) {A B : Solid}
    (k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ A)
    (f : A ⟶ B) :
    solidifiedFreeHomEquiv T B (k ≫ f) =
      ((isSolid.ι.map f).hom.app ⟨T⟩)
        (solidifiedFreeHomEquiv T A k) := by
  dsimp [solidifiedFreeHomEquiv]
  erw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  erw [GrothendieckTopology.yonedaEquiv_comp]

/-- Solidified free representables jointly separate solid objects. -/
lemma solidifiedFree_hom_ext
    {X Y : Solid} (f g : X ⟶ Y)
    (h : ∀ (T : LightProfinite)
      (k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ X),
      k ≫ f = k ≫ g) :
    f = g := by
  apply isSolid.ι.map_injective
  ext S x
  rcases S with ⟨T⟩
  let k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ X :=
    (solidifiedFreeHomEquiv T X).symm x
  have hk := h T k
  have hpoint := congrArg (solidifiedFreeHomEquiv T Y) hk
  change solidifiedFreeHomEquiv T Y (k ≫ f) = solidifiedFreeHomEquiv T Y (k ≫ g) at hpoint
  rw [solidifiedFreeHomEquiv_comp, solidifiedFreeHomEquiv_comp] at hpoint
  have hx : (solidifiedFreeHomEquiv T X) k = x := by
    dsimp [k]
    rw [Equiv.apply_symm_apply]
  rw [hx] at hpoint
  exact hpoint

/-- Enlarge a light profinite set by adding the convergent-sequence object.  This is infinite and
contains the original object as a coproduct summand. -/
noncomputable abbrev infiniteEnvelope (S : LightProfinite) : LightProfinite :=
  S ⨿ (ℕ∪{∞} : LightProfinite)

instance infiniteEnvelope_infinite (S : LightProfinite) : Infinite (infiniteEnvelope S) := by
  let f : (ℕ∪{∞} : LightProfinite) → ↑(infiniteEnvelope S).toTop := fun x =>
    (ConcreteCategory.hom (coprod.inr : (ℕ∪{∞} : LightProfinite) ⟶ infiniteEnvelope S)) x
  have hf : Function.Injective f := by
    dsimp [f, infiniteEnvelope]
    exact (CompHausLike.mono_iff_injective
      (coprod.inr : (ℕ∪{∞} : LightProfinite) ⟶ S ⨿ ℕ∪{∞})).mp inferInstance
  exact Infinite.of_injective (α := ↑(infiniteEnvelope S).toTop)
    (β := (ℕ∪{∞} : LightProfinite)) f hf

/-- The free object on `S` is a retract of the free object on its infinite envelope. -/
noncomputable def freeRetractIntoInfinite (S : LightProfinite) :
    Retract
      ((free ℤ).obj S.toCondensed)
      ((free ℤ).obj (infiniteEnvelope S).toCondensed) := by
  simpa [infiniteEnvelope] using
    CategoryTheory.functor_obj_retract_coprod
      (lightProfiniteToLightCondSet ⋙ free ℤ) S (ℕ∪{∞} : LightProfinite)

/-- The free-module map induced by the `n`th finite projection of a light profinite set. -/
noncomputable def freeProj (T : LightProfinite) (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj (T.component n).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (T.proj n)

/-- The constant map from the point to a light profinite space selecting `x`. -/
noncomputable def pointMap (X : LightProfinite) (x : X) :
    LightProfinite.of PUnit.{1} ⟶ X :=
  ConcreteCategory.ofHom ⟨fun _ => x, continuous_const⟩

@[simp]
lemma pointMap_apply (X : LightProfinite) (x : X) (u : LightProfinite.of PUnit.{1}) :
    pointMap X x u = x := rfl

/-- The free-module map induced by a point of a light profinite space. -/
noncomputable def freePointMap (T : LightProfinite) (t : T) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t)

@[simp]
lemma pointMap_comp (T S : LightProfinite) (f : T ⟶ S) (t : T) :
    pointMap T t ≫ f = pointMap S (f t) := by
  ext u
  rfl

lemma freePointMap_comp (T S : LightProfinite) (f : T ⟶ S) (t : T) :
    freePointMap T t ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map f =
      freePointMap S (f t) := by
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t) ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map f =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap S (f t))
  rw [← Functor.map_comp]
  rw [pointMap_comp]

lemma freePointMap_comp_freeProj (T : LightProfinite) (k : ℕ) (t : T) :
    freePointMap T t ≫ freeProj T k = freePointMap (T.component k) (T.proj k t) := by
  exact freePointMap_comp T (T.component k) (T.proj k) t

/-- The unique map from `T` to the point. -/
noncomputable def toPointMap (T : LightProfinite) : T ⟶ LightProfinite.of PUnit.{1} :=
  ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

@[simp]
lemma pointMap_point_eq_id : pointMap (LightProfinite.of PUnit.{1}) PUnit.unit = 𝟙 _ := by
  ext x

/-- A chosen point of `T`, followed by the map to the point, gives the identity on the free point. -/
lemma freePointMap_comp_toPointMap (T : LightProfinite) (t : T) :
    freePointMap T t ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) =
      𝟙 ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) := by
  rw [freePointMap_comp]
  dsimp [toPointMap]
  change freePointMap (LightProfinite.of PUnit.{1}) PUnit.unit = 𝟙 _
  dsimp [freePointMap]
  rw [pointMap_point_eq_id]
  simp

/-- A `ℤ`-valued map out of `ℤ[T]` factors through a finite quotient of `T`. -/
lemma zdisc_hom_factors_freeProj (T : LightProfinite)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    ∃ k : ℕ, ∃ ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc,
      freeProj T k ≫ ψ = φ := by
  let f : LocallyConstant T ℤ := zdiscSectionsEquiv T (freeHomEquivPoints T Zdisc φ)
  obtain ⟨k, g, hg⟩ := LightProfinite.exists_locallyConstant_factor_proj T f
  let ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc :=
    (freeHomEquivPoints (T.component k) Zdisc).symm
      ((zdiscSectionsEquiv (T.component k)).symm g)
  refine ⟨k, ψ, ?_⟩
  apply (freeHomEquivPoints T Zdisc).injective
  change freeHomEquivPoints T Zdisc
      (((free ℤ).map (lightProfiniteToLightCondSet.map (T.proj k))) ≫ ψ) =
    freeHomEquivPoints T Zdisc φ
  rw [freeHomEquivPoints_map]
  apply (zdiscSectionsEquiv T).injective
  rw [zdiscSectionsEquiv_map]
  dsimp [ψ, f] at hg ⊢
  rw [hg]
  simp

/-- If a sequence of endomorphisms is eventually killed by every finite quotient, then every
integer-valued evaluation is eventually zero. -/
lemma eventually_comp_zdisc_zero_of_eventually_freeProj_zero
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    ∀ᶠ n : ℕ in Filter.atTop, u n ≫ φ = 0 := by
  obtain ⟨k, ψ, hφ⟩ := zdisc_hom_factors_freeProj T φ
  filter_upwards [hu k] with n hn
  rw [← hφ]
  rw [← Category.assoc, hn]
  simp

/-- Maps from a free object to the discrete integers are determined by their values on ordinary
points. -/
lemma zdisc_hom_ext_of_points (T : LightProfinite)
    (f g : (free ℤ).obj T.toCondensed ⟶ Zdisc)
    (h : ∀ t : T, freePointMap T t ≫ f = freePointMap T t ≫ g) :
    f = g := by
  apply (freeHomEquivPoints T Zdisc).injective
  apply (zdiscSectionsEquiv T).injective
  ext t
  let pt : LightProfinite := LightProfinite.of PUnit.{1}
  have hp := congrArg (freeHomEquivPoints pt Zdisc) (h t)
  dsimp [freePointMap] at hp
  rw [freeHomEquivPoints_map, freeHomEquivPoints_map] at hp
  have hz := congrArg (zdiscSectionsEquiv pt) hp
  rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at hz
  exact congrFun (congrArg LocallyConstant.toFun hz) PUnit.unit

/-- The free-module endomorphism induced by the finite-rank retraction of an infinite test object. -/
noncomputable def freeFiniteApproxRetraction (T : LightProfinite) (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (LightProfinite.finiteApproxRetraction T n)

/-- The finite-rank free-module retraction agrees with the identity after projection to any earlier
finite stage. -/
lemma freeFiniteApproxRetraction_freeProj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    freeFiniteApproxRetraction T n ≫ freeProj T k = freeProj T k := by
  dsimp [freeFiniteApproxRetraction, freeProj]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.finiteApproxRetraction_proj_le T h]

/-- The tail endomorphisms used in Lemma 3.3.2: the zeroth term is the identity, and the successor
terms are `id -` the finite-rank approximations. -/
noncomputable def freeTailEndomorphism (T : LightProfinite) : ℕ →
    ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed)
  | 0 => 𝟙 _
  | n + 1 => 𝟙 _ - freeFiniteApproxRetraction T n

/-- Every fixed finite projection kills all sufficiently far tail endomorphisms. -/
lemma freeTailEndomorphism_succ_freeProj_zero (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    freeTailEndomorphism T (n + 1) ≫ freeProj T k = 0 := by
  dsimp [freeTailEndomorphism]
  rw [Preadditive.sub_comp]
  rw [Category.id_comp]
  rw [freeFiniteApproxRetraction_freeProj_le T h]
  abel

/-- Along every fixed finite quotient of `T`, the tail endomorphisms are eventually zero. -/
lemma freeTailEndomorphism_eventually_freeProj_zero (T : LightProfinite) (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, freeTailEndomorphism T n ≫ freeProj T k = 0 := by
  refine Filter.eventually_atTop.2 ⟨k + 1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ n =>
      apply freeTailEndomorphism_succ_freeProj_zero T
      omega

/-- The map from the point to `ℕ∪∞` selecting the natural number `n`. -/
noncomputable def natPoint (n : ℕ) : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => (n : ℕ∪{∞}), continuous_const⟩

@[simp]
lemma natPoint_comp_shift (n : ℕ) :
    natPoint n ≫ LightProfinite.shift = natPoint (n + 1) := by
  ext x
  rfl

/-- The slice map `T → (ℕ∪∞) × T` selecting the finite index `n`. -/
noncomputable def finiteTensorPoint (T : LightProfinite) (n : ℕ) :
    T ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  (λ_ T).inv ≫ natPoint n ▷ T

/-- The slice map `T → (ℕ∪∞) × T` selecting the point `∞`. -/
noncomputable def inftyTensorPoint (T : LightProfinite) :
    T ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  (λ_ T).inv ≫ ι ▷ T

@[simp]
lemma finiteTensorPoint_apply (T : LightProfinite) (n : ℕ) (t : T) :
    finiteTensorPoint T n t = ((n : ℕ∪{∞}), t) := rfl

@[simp]
lemma inftyTensorPoint_apply (T : LightProfinite) (t : T) :
    inftyTensorPoint T t = ((∞ : ℕ∪{∞}), t) := rfl

/-- The section `ℕ∪∞ → (ℕ∪∞) × T` choosing a fixed point of `T`. -/
noncomputable def ninfPointSection (T : LightProfinite) (t : T) :
    (ℕ∪{∞} : LightProfinite) ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  ConcreteCategory.ofHom ⟨fun a => (a, t), continuous_id.prodMk continuous_const⟩

@[simp]
lemma natPoint_comp_ninfPointSection (T : LightProfinite) (t : T) (n : ℕ) :
    natPoint n ≫ ninfPointSection T t = pointMap T t ≫ finiteTensorPoint T n := by
  ext u <;> rfl

@[simp]
lemma iota_comp_ninfPointSection (T : LightProfinite) (t : T) :
    ι ≫ ninfPointSection T t = pointMap T t ≫ inftyTensorPoint T := by
  ext u <;> rfl

/-- A finite natural-number point is open in `ℕ∪∞`. -/
lemma finite_nat_singleton_open (n : ℕ) : IsOpen ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) := by
  simpa using (OnePoint.isOpen_image_coe (X := ℕ) (s := ({n} : Set ℕ))).2
    (isOpen_discrete _)

/-- The standard tail neighborhood `{∞} ∪ {n | N ≤ n}` is open in `ℕ∪∞`. -/
lemma ninf_tail_open (N : ℕ) :
    IsOpen ({a : ℕ∪{∞} | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n} :
      Set ℕ∪{∞}) := by
  let A : Set (ℕ∪{∞}) := {a | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n}
  have hinfty : (∞ : ℕ∪{∞}) ∈ A := by simp [A]
  have hpre : ((↑) : ℕ → ℕ∪{∞}) ⁻¹' A = {n : ℕ | N ≤ n} := by
    ext n
    simp [A]
  have hcompact : IsCompact (((↑) : ℕ → ℕ∪{∞}) ⁻¹' A)ᶜ := by
    rw [hpre]
    have hfin : Set.Finite ({n : ℕ | n < N}) := Set.finite_lt_nat N
    have hset : ({n : ℕ | N ≤ n} : Set ℕ)ᶜ = {n : ℕ | n < N} := by
      ext n
      simp [not_le]
    rw [hset]
    exact isCompact_iff_finite.mpr hfin
  have hopenpre : IsOpen (((↑) : ℕ → ℕ∪{∞}) ⁻¹' A) := by
    rw [hpre]
    exact isOpen_discrete _
  have hA : IsOpen A := (OnePoint.isOpen_iff_of_mem' hinfty).2 ⟨hcompact, hopenpre⟩
  simpa [A] using hA

/-- A sequence of locally constant integer-valued functions that is eventually zero extends by zero
across `∞`. -/
lemma ninfLocallyConstant_fun_isLocallyConstant
    (T : LightProfinite) (f : ℕ → LocallyConstant T ℤ)
    (N : ℕ) (hN : ∀ n : ℕ, N ≤ n → f n = 0) :
    IsLocallyConstant (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) =>
      match x.1 with
      | ∞ => (0 : ℤ)
      | OnePoint.some n => f n x.2) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      let A : Set (ℕ∪{∞}) := {a | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n}
      refine ⟨Set.prod A Set.univ, ?_, ?_, ?_⟩
      · exact (ninf_tail_open N).prod isOpen_univ
      · exact ⟨by simp [A], trivial⟩
      · rintro ⟨a', t'⟩ h
        rcases h with ⟨ha', _⟩
        rcases ha' with rfl | ⟨n, hn_eq, hn_le⟩
        · rfl
        · cases hn_eq
          change f n t' = 0
          rw [hN n hn_le]
          rfl
  | coe n =>
      obtain ⟨U, hUopen, htU, hUconst⟩ := (f n).isLocallyConstant.exists_open t
      refine ⟨Set.prod ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) U, ?_, ?_, ?_⟩
      · exact (finite_nat_singleton_open n).prod hUopen
      · exact ⟨rfl, htU⟩
      · rintro ⟨a', t'⟩ h
        rcases h with ⟨ha', ht'⟩
        have haeq : a' = (n : ℕ∪{∞}) := by simpa using ha'
        cases haeq
        change f n t' = f n t
        exact hUconst t' ht'

/-- Extend an eventually-zero sequence of locally constant integer-valued functions on `T` to a
locally constant function on `(ℕ∪∞) × T`, with value zero on the `∞` slice. -/
noncomputable def ninfLocallyConstantOfEventuallyZero
    (T : LightProfinite) (f : ℕ → LocallyConstant T ℤ)
    (hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0) :
    LocallyConstant (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)) ℤ :=
  let N := Classical.choose (Filter.eventually_atTop.1 hf)
  have hN : ∀ n : ℕ, N ≤ n → f n = 0 := Classical.choose_spec (Filter.eventually_atTop.1 hf)
  ⟨fun x => match x.1 with
    | ∞ => (0 : ℤ)
    | OnePoint.some n => f n x.2,
    ninfLocallyConstant_fun_isLocallyConstant T f N hN⟩

@[simp]
lemma ninfLocallyConstantOfEventuallyZero_finite
    (T : LightProfinite) (f : ℕ → LocallyConstant T ℤ)
    (hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0) (n : ℕ) :
    (ninfLocallyConstantOfEventuallyZero T f hf).comap (finiteTensorPoint T n).hom.hom = f n := by
  dsimp [ninfLocallyConstantOfEventuallyZero]
  ext t
  rfl

@[simp]
lemma ninfLocallyConstantOfEventuallyZero_infty
    (T : LightProfinite) (f : ℕ → LocallyConstant T ℤ)
    (hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0) :
    (ninfLocallyConstantOfEventuallyZero T f hf).comap (inftyTensorPoint T).hom.hom = 0 := by
  dsimp [ninfLocallyConstantOfEventuallyZero]
  ext t
  rfl

/-- A sequence of `ℤ`-valued maps out of `ℤ[T]` that is eventually zero gives a `Zdisc`-section
over `(ℕ∪∞) × T`, extended by zero at `∞`. -/
noncomputable def zdiscSectionOverNinfOfEventuallyZero
    (T : LightProfinite)
    (v : ℕ → ((free ℤ).obj T.toCondensed ⟶ Zdisc))
    (hv : ∀ᶠ n : ℕ in Filter.atTop, v n = 0) :
    Zdisc.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  let f : ℕ → LocallyConstant T ℤ := fun n =>
    zdiscSectionsEquiv T (freeHomEquivPoints T Zdisc (v n))
  have hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0 := by
    filter_upwards [hv] with n hn
    dsimp [f]
    rw [hn]
    simp
  (zdiscSectionsEquiv (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite))).symm
    (ninfLocallyConstantOfEventuallyZero T f hf)

/-- Finite slices of the zero-extended `Zdisc`-section recover the original sequence. -/
lemma zdiscSectionOverNinfOfEventuallyZero_finite
    (T : LightProfinite)
    (v : ℕ → ((free ℤ).obj T.toCondensed ⟶ Zdisc))
    (hv : ∀ᶠ n : ℕ in Filter.atTop, v n = 0) (n : ℕ) :
    (freeHomEquivPoints T Zdisc).symm
      (Zdisc.obj.map (finiteTensorPoint T n).op
        (zdiscSectionOverNinfOfEventuallyZero T v hv)) = v n := by
  apply (freeHomEquivPoints T Zdisc).injective
  rw [Equiv.apply_symm_apply]
  apply (zdiscSectionsEquiv T).injective
  rw [zdiscSectionsEquiv_map]
  dsimp [zdiscSectionOverNinfOfEventuallyZero]
  rw [Equiv.apply_symm_apply]
  simp

/-- The `∞` slice of the zero-extended `Zdisc`-section is zero. -/
lemma zdiscSectionOverNinfOfEventuallyZero_infty
    (T : LightProfinite)
    (v : ℕ → ((free ℤ).obj T.toCondensed ⟶ Zdisc))
    (hv : ∀ᶠ n : ℕ in Filter.atTop, v n = 0) :
    (freeHomEquivPoints T Zdisc).symm
      (Zdisc.obj.map (inftyTensorPoint T).op
        (zdiscSectionOverNinfOfEventuallyZero T v hv)) = 0 := by
  apply (freeHomEquivPoints T Zdisc).injective
  rw [Equiv.apply_symm_apply]
  apply (zdiscSectionsEquiv T).injective
  rw [zdiscSectionsEquiv_map]
  dsimp [zdiscSectionOverNinfOfEventuallyZero]
  rw [Equiv.apply_symm_apply]
  simp

/-- Applying an integer-valued functional to a null sequence of endomorphisms gives the corresponding
zero-extended `Zdisc`-section over `(ℕ∪∞) × T`. -/
noncomputable def zdiscSectionOverNinfOfEventuallyFreeProjZero
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    Zdisc.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  zdiscSectionOverNinfOfEventuallyZero T (fun n => u n ≫ φ)
    (eventually_comp_zdisc_zero_of_eventually_freeProj_zero T u hu φ)

lemma zdiscSectionOverNinfOfEventuallyFreeProjZero_finite
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) (n : ℕ) :
    (freeHomEquivPoints T Zdisc).symm
      (Zdisc.obj.map (finiteTensorPoint T n).op
        (zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ)) = u n ≫ φ :=
  zdiscSectionOverNinfOfEventuallyZero_finite T (fun n => u n ≫ φ)
    (eventually_comp_zdisc_zero_of_eventually_freeProj_zero T u hu φ) n

lemma zdiscSectionOverNinfOfEventuallyFreeProjZero_infty
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    (freeHomEquivPoints T Zdisc).symm
      (Zdisc.obj.map (inftyTensorPoint T).op
        (zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ)) = 0 :=
  zdiscSectionOverNinfOfEventuallyZero_infty T (fun n => u n ≫ φ)
    (eventually_comp_zdisc_zero_of_eventually_freeProj_zero T u hu φ)

/-- The `n`th finite-point generator in the free object on `ℕ∪∞`. -/
noncomputable def freeNatBasis (n : ℕ) :
    𝟙_ LightCondAb ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  freePointIsoUnit.inv ≫
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeNatBasis_comp_shift (n : ℕ) :
    freeNatBasis n ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
      freeNatBasis (n + 1) := by
  dsimp [freeNatBasis]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint (n + 1)))
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [natPoint_comp_shift]

set_option backward.isDefEq.respectTransparency false in
lemma freeNatBasis_oneMinusShift' (n : ℕ) :
    freeNatBasis n ≫ oneMinusShift' ℤ = freeNatBasis n - freeNatBasis (n + 1) := by
  dsimp [oneMinusShift']
  change freeNatBasis n ≫
      (𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj (ℕ∪{∞})) -
        (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift) =
    freeNatBasis n - freeNatBasis (n + 1)
  rw [Preadditive.comp_sub]
  rw [freeNatBasis_comp_shift]
  change freeNatBasis n - freeNatBasis (n + 1) = freeNatBasis n - freeNatBasis (n + 1)
  rfl

/-- The `∞` generator in the free object on `ℕ∪∞`. -/
noncomputable def freeInftyBasis :
    𝟙_ LightCondAb ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  freePointIsoUnit.inv ≫ P_map ℤ

@[simp]
lemma iota_comp_shift : ι ≫ LightProfinite.shift = ι := by
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeInftyBasis_comp_shift :
    freeInftyBasis ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
      freeInftyBasis := by
  dsimp [freeInftyBasis, P_map]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map ι) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
    (free ℤ).map (lightProfiniteToLightCondSet.map ι)
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [iota_comp_shift]

set_option backward.isDefEq.respectTransparency false in
lemma freeInftyBasis_oneMinusShift' :
    freeInftyBasis ≫ oneMinusShift' ℤ = 0 := by
  dsimp [oneMinusShift']
  change freeInftyBasis ≫
      (𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj (ℕ∪{∞})) -
        (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift) = 0
  rw [Preadditive.comp_sub]
  rw [freeInftyBasis_comp_shift]
  change freeInftyBasis - freeInftyBasis = 0
  abel

/-- The class in `P ℤ` represented by the `n`th finite point of `ℕ∪∞`. -/
noncomputable def pBasis (n : ℕ) : 𝟙_ LightCondAb ⟶ P ℤ :=
  freeNatBasis n ≫ P_proj ℤ

/-- The zeroth-coordinate section used for the tail map in Lemma 3.3.2. -/
noncomputable def tailSection (T : LightProfinite) :
    (free ℤ).obj T.toCondensed ⟶ P ℤ ⊗ (free ℤ).obj T.toCondensed :=
  (λ_ ((free ℤ).obj T.toCondensed)).inv ≫ pBasis 0 ▷ (free ℤ).obj T.toCondensed

/-- The `n`th finite slice of a numerator map `ℤ[ℕ∪∞] ⊗ M ⟶ N`. -/
noncomputable def numeratorSlice (M N : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) : M ⟶ N :=
  (λ_ M).inv ≫ freeNatBasis n ▷ M ≫ f

@[reassoc]
lemma numeratorSlice_comp (M N K : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) (g : N ⟶ K) :
    numeratorSlice M K n (f ≫ g) = numeratorSlice M N n f ≫ g := by
  dsimp [numeratorSlice]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Slicing after precomposition by `1 - shift` takes finite differences of slices. -/
lemma numeratorSlice_oneMinusShift' (M N : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    numeratorSlice M N n ((oneMinusShift' ℤ ▷ M) ≫ f) =
      numeratorSlice M N n f - numeratorSlice M N (n + 1) f := by
  dsimp [numeratorSlice]
  rw [← comp_whiskerRight_assoc]
  rw [freeNatBasis_oneMinusShift']
  rw [IntProof.sub_whiskerRight]
  rw [Preadditive.sub_comp]
  rw [Preadditive.comp_sub]

/-- The `n`th finite value of a map out of the free object on `ℕ∪∞`. -/
noncomputable def freeNatValue (N : LightCondAb) (n : ℕ)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ N :=
  (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫ f

/-- The `n`th finite value of a map built from a section over `ℕ∪∞` is obtained by restricting
that section to the point `n`. -/
lemma freeNatValue_of_freeElement (A : LightCondAb) (n : ℕ)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩) :
    freeNatValue A n ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) =
      (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm
        (A.obj.map (natPoint n).op x) := by
  dsimp [freeNatValue]
  rw [freeHomEquivPoints_symm_map]

/-- The `∞` value of a map out of the free object on `ℕ∪∞`. -/
noncomputable def freeInftyValue (N : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N) : 𝟙_ LightCondAb ⟶ N :=
  freeInftyBasis ≫ f

/-- The `∞` value of a map built from a section over `ℕ∪∞` is obtained by restricting that
section to the point `∞`. -/
lemma freeInftyValue_of_freeElement (A : LightCondAb)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩) :
    freeInftyValue A ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) =
      freePointIsoUnit.inv ≫
        (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm (A.obj.map ι.op x) := by
  dsimp [freeInftyValue, freeInftyBasis, P_map]
  rw [Category.assoc]
  rw [freeHomEquivPoints_symm_map]

/-- A section over `ℕ∪∞` whose restriction to `∞` is zero gives a free numerator with zero
`∞` value. -/
lemma freeInftyValue_zero_of_element_infty (A : LightCondAb)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩)
    (h : (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm (A.obj.map ι.op x) = 0) :
    freeInftyValue A ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) = 0 := by
  rw [freeInftyValue_of_freeElement]
  rw [h]
  simp

/-- If a map out of `ℤ[ℕ∪∞]` is zero at `∞`, then it kills the denominator defining `P ℤ`. -/
lemma freeNumerator_kills_of_inftyValue_zero (N : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N)
    (h : freeInftyValue N f = 0) :
    P_map ℤ ≫ f = 0 := by
  haveI : IsIso freePointIsoUnit.inv := by infer_instance
  apply (cancel_epi freePointIsoUnit.inv).1
  dsimp [freeInftyValue, freeInftyBasis] at h ⊢
  simpa [Category.assoc] using h

/-- The `∞` slice of a numerator map `ℤ[ℕ∪∞] ⊗ M ⟶ N`. -/
noncomputable def inftySlice (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) : M ⟶ N :=
  (λ_ M).inv ≫ freeInftyBasis ▷ M ≫ f

@[reassoc]
lemma inftySlice_comp (M N K : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) (g : N ⟶ K) :
    inftySlice M K (f ≫ g) = inftySlice M N f ≫ g := by
  dsimp [inftySlice]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The `∞` slice after precomposition by `1 - shift` is zero. -/
lemma inftySlice_oneMinusShift' (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    inftySlice M N ((oneMinusShift' ℤ ▷ M) ≫ f) = 0 := by
  dsimp [inftySlice]
  rw [← comp_whiskerRight_assoc]
  rw [freeInftyBasis_oneMinusShift']
  simp

/-- If the `∞` slice of a numerator is zero, then it kills the denominator defining `P ℤ`. -/
lemma numerator_kills_of_inftySlice_zero (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (h : inftySlice M N f = 0) :
    (P_map ℤ ▷ M) ≫ f = 0 := by
  let u : M ⟶ (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⊗ M :=
    (λ_ M).inv ≫ freePointIsoUnit.inv ▷ M
  haveI : IsIso u := by dsimp [u]; infer_instance
  apply (cancel_epi u).1
  calc
    u ≫ ((P_map ℤ ▷ M) ≫ f)
        = inftySlice M N f := by
          dsimp [u, inftySlice, freeInftyBasis]
          simp only [Category.assoc]
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = u ≫ (0 : (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⊗ M ⟶ N) := by
          rw [h]
          simp

/-- Descend a map out of `ℤ[ℕ∪∞] ⊗ M` which kills the basepoint summand to a map out of
`P ℤ ⊗ M`. -/
noncomputable def pTensorDesc (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) :
    P ℤ ⊗ M ⟶ N := by
  refine (PreservesCoequalizer.iso (tensorRight M) (P_map ℤ) 0).inv ≫ coequalizer.desc f ?_
  rw [Functor.map_zero, zero_comp]
  exact hf

set_option backward.isDefEq.respectTransparency false in
lemma epi_P_proj_tensor (M : LightCondAb) : Epi (P_proj ℤ ▷ M) := by
  change Epi ((tensorRight M).map (coequalizer.π (P_map ℤ) 0))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pTensorDesc_comp_proj (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) :
    (P_proj ℤ ▷ M) ≫ pTensorDesc M N f hf = f := by
  dsimp [pTensorDesc, P_proj]
  simpa using (map_π_preserves_coequalizer_inv_desc (G := tensorRight M)
    (f := P_map ℤ) (g := 0) (k := f) (by rw [Functor.map_zero, zero_comp]; exact hf))

/-- Slicing a descended numerator at a finite basis element recovers the corresponding numerator
slice. -/
lemma pTensorDesc_slice (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) (n : ℕ) :
    ((λ_ M).inv ≫ pBasis n ▷ M) ≫ pTensorDesc M N f hf =
      numeratorSlice M N n f := by
  dsimp [pBasis, numeratorSlice]
  simp only [Category.assoc]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [pTensorDesc_comp_proj]

-- The free tensor isomorphism is natural in the left variable.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_naturality_left {A' A S : LightProfinite} (φ : A' ⟶ A) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map φ) ▷ (free ℤ).obj S.toCondensed) ≫
        (IntProof.freeTensorIsoInt A S).hom =
      (IntProof.freeTensorIsoInt A' S).hom ≫
        (free ℤ).map (lightProfiniteToLightCondSet.map (φ ⊗ₘ 𝟙 S)) := by
  dsimp [IntProof.freeTensorIsoInt]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc (free ℤ)
    (lightProfiniteToLightCondSet.map φ) S.toCondensed
    ((free ℤ).map (Functor.LaxMonoidal.μ lightProfiniteToLightCondSet A S))]
  slice_lhs 2 4 => rw [← Functor.map_comp]
  slice_rhs 2 4 => rw [← Functor.map_comp]
  rw [Functor.LaxMonoidal.μ_natural_left lightProfiniteToLightCondSet]
  simp [MonoidalCategory.tensorHom_id]

-- The free tensor isomorphism is compatible with the left unit after identifying the chosen
-- point-object with the tensor unit.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_leftUnit (T : LightProfinite) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freePointIsoUnit.inv ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (LightProfinite.of PUnit.{1}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (λ_ T).inv) := by
  dsimp [IntProof.freeTensorIsoInt, freePointIsoUnit]
  simp [← Functor.map_comp]
  change (free ℤ).map
      ((λ_ (lightProfiniteToLightCondSet.obj T)).inv ≫
        (Functor.LaxMonoidal.ε lightProfiniteToLightCondSet ▷ lightProfiniteToLightCondSet.obj T) ≫
          Functor.LaxMonoidal.μ lightProfiniteToLightCondSet (𝟙_ LightProfinite) T) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (λ_ T).inv)
  rw [Functor.LaxMonoidal.left_unitality_inv]

-- Compatibility of the free tensor isomorphism with finite slices.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_finiteTensorPoint (T : LightProfinite) (n : ℕ) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freeNatBasis n ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (finiteTensorPoint T n)) := by
  dsimp [freeNatBasis]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [freeTensorIsoInt_hom_naturality_left]
  rw [freeTensorIsoInt_hom_leftUnit_assoc]
  dsimp [finiteTensorPoint]
  rw [← Functor.map_comp]
  congr 1

-- Compatibility of the free tensor isomorphism with the `∞` slice.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_inftyTensorPoint (T : LightProfinite) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freeInftyBasis ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (inftyTensorPoint T)) := by
  dsimp [freeInftyBasis, P_map]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [freeTensorIsoInt_hom_naturality_left]
  rw [freeTensorIsoInt_hom_leftUnit_assoc]
  dsimp [inftyTensorPoint]
  rw [← Functor.map_comp]
  congr 1

/-- Finite slices of a numerator built from a section over `(ℕ∪∞) × T` are obtained by
restricting that section along the finite slice map. -/
lemma numeratorSlice_of_freeTensorElement (T : LightProfinite) (A : LightCondAb) (n : ℕ)
    (x : A.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩) :
    numeratorSlice ((free ℤ).obj T.toCondensed) A n
      ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
        (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x) =
      (freeHomEquivPoints T A).symm (A.obj.map (finiteTensorPoint T n).op x) := by
  dsimp [numeratorSlice]
  rw [freeTensorIsoInt_hom_finiteTensorPoint_assoc]
  rw [freeHomEquivPoints_symm_map]

/-- The `∞` slice of a numerator built from a section over `(ℕ∪∞) × T` is obtained by
restricting that section along the `∞` slice map. -/
lemma inftySlice_of_freeTensorElement (T : LightProfinite) (A : LightCondAb)
    (x : A.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩) :
    inftySlice ((free ℤ).obj T.toCondensed) A
      ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
        (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x) =
      (freeHomEquivPoints T A).symm (A.obj.map (inftyTensorPoint T).op x) := by
  dsimp [inftySlice]
  rw [freeTensorIsoInt_hom_inftyTensorPoint_assoc]
  rw [freeHomEquivPoints_symm_map]

/-- Finite slices of an arbitrary numerator can be read from the corresponding section over
`(ℕ∪∞) × T`. -/
lemma numeratorSlice_eq_symm_map_finite (T : LightProfinite) (A : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ A) :
    numeratorSlice ((free ℤ).obj T.toCondensed) A n f =
      (freeHomEquivPoints T A).symm
        (A.obj.map (finiteTensorPoint T n).op
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
            ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f))) := by
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  have hf : f = (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
      (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x := by
    dsimp [x]
    simp
  change numeratorSlice ((free ℤ).obj T.toCondensed) A n f =
      (freeHomEquivPoints T A).symm (A.obj.map (finiteTensorPoint T n).op x)
  rw [hf]
  rw [numeratorSlice_of_freeTensorElement]

/-- The `∞` slice of an arbitrary numerator can be read from the corresponding section over
`(ℕ∪∞) × T`. -/
lemma inftySlice_eq_symm_map_infty (T : LightProfinite) (A : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ A) :
    inftySlice ((free ℤ).obj T.toCondensed) A f =
      (freeHomEquivPoints T A).symm
        (A.obj.map (inftyTensorPoint T).op
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
            ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f))) := by
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  have hf : f = (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
      (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x := by
    dsimp [x]
    simp
  change inftySlice ((free ℤ).obj T.toCondensed) A f =
      (freeHomEquivPoints T A).symm (A.obj.map (inftyTensorPoint T).op x)
  rw [hf]
  rw [inftySlice_of_freeTensorElement]

/-- Sections of `ℤ` over `(ℕ∪∞) × T` are determined by all finite slices and the `∞` slice. -/
lemma zdisc_section_ext_of_slices (T : LightProfinite)
    (x y : Zdisc.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩)
    (hfinite : ∀ n : ℕ,
      Zdisc.obj.map (finiteTensorPoint T n).op x =
        Zdisc.obj.map (finiteTensorPoint T n).op y)
    (hinfty : Zdisc.obj.map (inftyTensorPoint T).op x =
      Zdisc.obj.map (inftyTensorPoint T).op y) :
    x = y := by
  apply (zdiscSectionsEquiv ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)).injective
  ext p
  rcases p with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      have h := congrArg (zdiscSectionsEquiv T) hinfty
      rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at h
      exact congrFun (congrArg LocallyConstant.toFun h) t
  | coe n =>
      have h := congrArg (zdiscSectionsEquiv T) (hfinite n)
      rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at h
      exact congrFun (congrArg LocallyConstant.toFun h) t

/-- Obligation: finite free objects are separated by their integer-valued linear functionals.
This is the finite-rank algebraic core of `freeTarget_section_ext_of_finite_zdisc_eval`. -/
lemma finiteFree_section_ext_of_zdisc_eval (F S : LightProfinite) [Finite F]
    (x y : ((free ℤ).obj F.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ ψ : (free ℤ).obj F.toCondensed ⟶ Zdisc,
      ψ.hom.app ⟨S⟩ x = ψ.hom.app ⟨S⟩ y) :
    x = y := by
  sorry

/-- Obligation: the finite projections in the chosen AsLimit presentation jointly separate
sections of the free object `ℤ[T]`. -/
lemma freeTarget_section_ext_of_finite_proj (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ k : ℕ,
      (freeProj T k).hom.app ⟨S⟩ x = (freeProj T k).hom.app ⟨S⟩ y) :
    x = y := by
  sorry

/-- Sections of the free object `ℤ[T]` are separated by integer-valued functions that factor through
finite quotients of `T`, reduced to finite-rank separation and joint separation of finite
projections. -/
lemma freeTarget_section_ext_of_finite_zdisc_eval (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ k : ℕ, ∀ ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc,
      (freeProj T k ≫ ψ).hom.app ⟨S⟩ x = (freeProj T k ≫ ψ).hom.app ⟨S⟩ y) :
    x = y := by
  apply freeTarget_section_ext_of_finite_proj T S
  intro k
  apply finiteFree_section_ext_of_zdisc_eval (T.component k) S
  intro ψ
  exact h k ψ

/-- Sections of the free object `ℤ[T]` are separated by all locally constant integer-valued
functions on `T`, reduced to finite-stage integer-valued evaluations. -/
lemma freeTarget_section_ext_of_zdisc_eval (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y) :
    x = y := by
  apply freeTarget_section_ext_of_finite_zdisc_eval T S
  intro k ψ
  exact h (freeProj T k ≫ ψ)

/-- Endomorphisms of the free object `ℤ[T]` are determined by their composites with the free point
maps.  The proof reduces to the existing `Zdisc`-valued separation obligation. -/
lemma freeTarget_hom_ext_of_points (T : LightProfinite)
    (f g : (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed)
    (h : ∀ t : T, freePointMap T t ≫ f = freePointMap T t ≫ g) :
    f = g := by
  apply (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).injective
  apply freeTarget_section_ext_of_zdisc_eval T T
  intro φ
  rw [← freeHomEquivPoints_comp T f φ]
  rw [← freeHomEquivPoints_comp T g φ]
  congr 1
  apply zdisc_hom_ext_of_points
  intro t
  change (freePointMap T t ≫ f) ≫ φ = (freePointMap T t ≫ g) ≫ φ
  rw [h t]

/-- Sections of the free object `ℤ[T]` over `(ℕ∪∞) × T` are determined by all finite slices and
 the `∞` slice, assuming the standard separation of `ℤ[T]` by `ℤ`-valued functions. -/
lemma freeTarget_section_ext_of_slices (T : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩)
    (hfinite : ∀ n : ℕ,
      ((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op x =
        ((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op y)
    (hinfty : ((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op x =
      ((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op y) :
    x = y := by
  apply freeTarget_section_ext_of_zdisc_eval
  intro φ
  apply zdisc_section_ext_of_slices T
  · intro n
    rw [← LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op x]
    rw [← LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op y]
    rw [hfinite]
  · rw [← LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op x]
    rw [← LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op y]
    rw [hinfty]

/-- Maps from `ℤ[(ℕ∪∞) × T]` to `ℤ[T]` are determined by all finite slices and the `∞` slice. -/
lemma freeTarget_numerator_ext_of_slices (T : LightProfinite)
    (f g : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj T.toCondensed)
    (hfinite : ∀ n : ℕ,
      numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n f =
        numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n g)
    (hinfty : inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) f =
      inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) g) :
    f = g := by
  let A := (free ℤ).obj T.toCondensed
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  let y := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ g)
  have hxy : x = y := by
    apply freeTarget_section_ext_of_slices T
    · intro n
      have h := congrArg (freeHomEquivPoints T A) (hfinite n)
      rw [numeratorSlice_eq_symm_map_finite, numeratorSlice_eq_symm_map_finite] at h
      simpa [A, x, y] using h
    · have h := congrArg (freeHomEquivPoints T A) hinfty
      rw [inftySlice_eq_symm_map_infty, inftySlice_eq_symm_map_infty] at h
      simpa [A, x, y] using h
  have hmaps : (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f =
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ g := by
    apply (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).injective
    exact hxy
  apply (cancel_epi (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv).1
  exact hmaps

/-- Obligation: the remaining realization part of the AsLimit/compactness bridge.  The
`Zdisc`-valued evaluations of a null sequence of endomorphisms have already been constructed
explicitly; this obligation asks that those compatible evaluations come from an actual section of
`ℤ[T]` over `(ℕ∪∞) × T`. -/
lemma exists_freeSectionOverNinf_realizing_zdisc_evaluations
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj
        ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩,
      ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
        φ.hom.app ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ x =
          zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ := by
  sorry

/-- The section realizing all `Zdisc` evaluations of a null endomorphism sequence is unique, once it
exists. -/
lemma freeSectionOverNinf_realizing_zdisc_evaluations_unique
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    {x y : ((free ℤ).obj T.toCondensed).obj.obj
        ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩}
    (hx : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
        φ.hom.app ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ x =
          zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ)
    (hy : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
        φ.hom.app ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ y =
          zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ) :
    x = y := by
  apply freeTarget_section_ext_of_zdisc_eval T (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite))
  intro φ
  rw [hx φ, hy φ]

/-- The AsLimit/compactness bridge turning a sequence of endomorphisms of `ℤ[T]` which is
eventually zero after every finite quotient of `T` into a continuous section over `(ℕ∪∞) × T`,
with prescribed finite slices and zero `∞` slice.  The finite/∞ slice verification is formal from
the `Zdisc`-evaluation realization and the free-target separation obligation. -/
lemma exists_freeSectionOverNinf_of_eventually_freeProj_zero
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj
        ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op x) = u n) ∧
      (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op x) = 0 := by
  let A := (free ℤ).obj T.toCondensed
  obtain ⟨x, hx⟩ := exists_freeSectionOverNinf_realizing_zdisc_evaluations T u hu
  refine ⟨x, ?_, ?_⟩
  · intro n
    apply (freeHomEquivPoints T A).injective
    rw [Equiv.apply_symm_apply]
    apply freeTarget_section_ext_of_zdisc_eval T T
    intro φ
    rw [LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op x]
    rw [hx φ]
    have hY := congrArg (freeHomEquivPoints T Zdisc)
      (zdiscSectionOverNinfOfEventuallyFreeProjZero_finite T u hu φ n)
    rw [Equiv.apply_symm_apply] at hY
    rw [freeHomEquivPoints_comp] at hY
    exact hY
  · apply (freeHomEquivPoints T A).injective
    rw [Equiv.apply_symm_apply]
    change A.obj.map (inftyTensorPoint T).op x = (0 : A.obj.obj ⟨T⟩)
    apply freeTarget_section_ext_of_zdisc_eval T T
    intro φ
    rw [LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op x]
    rw [hx φ]
    have hY := congrArg (freeHomEquivPoints T Zdisc)
      (zdiscSectionOverNinfOfEventuallyFreeProjZero_infty T u hu φ)
    rw [Equiv.apply_symm_apply] at hY
    simpa using hY

/-- The section over `(ℕ∪∞) × T` associated to a null sequence of endomorphisms of `ℤ[T]`. -/
noncomputable def freeSectionOverNinfOfNullSequence
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) :
    ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  (exists_freeSectionOverNinf_of_eventually_freeProj_zero T u hu).choose

/-- Finite slices of the section associated to a null sequence are the prescribed endomorphisms. -/
lemma freeSectionOverNinfOfNullSequence_finite
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) (n : ℕ) :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op
        (freeSectionOverNinfOfNullSequence T u hu)) = u n :=
  ((exists_freeSectionOverNinf_of_eventually_freeProj_zero T u hu).choose_spec).1 n

/-- The section associated to a null sequence has zero `∞` slice. -/
lemma freeSectionOverNinfOfNullSequence_infty
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op
        (freeSectionOverNinfOfNullSequence T u hu)) = 0 :=
  ((exists_freeSectionOverNinf_of_eventually_freeProj_zero T u hu).choose_spec).2

/-- After applying any integer-valued functional, the chosen free null-section is the explicit
zero-extended `Zdisc`-section. -/
lemma freeSectionOverNinfOfNullSequence_zdisc_eval
    (T : LightProfinite)
    (u : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    φ.hom.app ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩
      (freeSectionOverNinfOfNullSequence T u hu) =
        zdiscSectionOverNinfOfEventuallyFreeProjZero T u hu φ := by
  apply zdisc_section_ext_of_slices T
  · intro n
    rw [← LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op
      (freeSectionOverNinfOfNullSequence T u hu)]
    have hX := congrArg (freeHomEquivPoints T ((free ℤ).obj T.toCondensed))
      (freeSectionOverNinfOfNullSequence_finite T u hu n)
    rw [Equiv.apply_symm_apply] at hX
    have hY := congrArg (freeHomEquivPoints T Zdisc)
      (zdiscSectionOverNinfOfEventuallyFreeProjZero_finite T u hu φ n)
    rw [Equiv.apply_symm_apply] at hY
    rw [freeHomEquivPoints_comp] at hY
    rw [hX]
    exact hY.symm
  · rw [← LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op
      (freeSectionOverNinfOfNullSequence T u hu)]
    have hX := congrArg (freeHomEquivPoints T ((free ℤ).obj T.toCondensed))
      (freeSectionOverNinfOfNullSequence_infty T u hu)
    rw [Equiv.apply_symm_apply] at hX
    have hY := congrArg (freeHomEquivPoints T Zdisc)
      (zdiscSectionOverNinfOfEventuallyFreeProjZero_infty T u hu φ)
    rw [Equiv.apply_symm_apply] at hY
    rw [hX]
    simpa using hY.symm

/-- The section of `ℤ[T]` over `(ℕ∪∞) × T` whose finite slices are the tail endomorphisms and
whose `∞` slice is zero. -/
noncomputable def infiniteTailElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  freeSectionOverNinfOfNullSequence T (freeTailEndomorphism T)
    (freeTailEndomorphism_eventually_freeProj_zero T)

/-- The numerator of the tail map, built from its section over `(ℕ∪∞) × T`. -/
noncomputable def infiniteTailNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
      ((free ℤ).obj T.toCondensed)).symm (infiniteTailElement T)

/-- Restricting `infiniteTailElement` to the finite slice `n` gives the `n`th tail
endomorphism. -/
lemma infiniteTailElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op
        (infiniteTailElement T)) =
      freeTailEndomorphism T n := by
  dsimp [infiniteTailElement]
  exact freeSectionOverNinfOfNullSequence_finite T (freeTailEndomorphism T)
    (freeTailEndomorphism_eventually_freeProj_zero T) n

/-- Finite slices of the tail numerator are the prescribed tail endomorphisms. -/
lemma infiniteTailNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteTailNumerator T) = freeTailEndomorphism T n := by
  rw [infiniteTailNumerator, numeratorSlice_of_freeTensorElement]
  exact infiniteTailElement_finite T n

/-- Restricting `infiniteTailElement` to the `∞` slice gives zero. -/
lemma infiniteTailElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op
        (infiniteTailElement T)) = 0 := by
  dsimp [infiniteTailElement]
  exact freeSectionOverNinfOfNullSequence_infty T (freeTailEndomorphism T)
    (freeTailEndomorphism_eventually_freeProj_zero T)

/-- The `∞` slice of the tail numerator is zero. -/
lemma infiniteTailNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteTailNumerator T) = 0 := by
  rw [infiniteTailNumerator, inftySlice_of_freeTensorElement]
  exact infiniteTailElement_infty T

/-- The tail numerator vanishes on the basepoint summand, so it descends through `P ℤ ⊗ ℤ[T]`. -/
lemma infiniteTailNumerator_kills (T : LightProfinite) [Infinite T] :
    (P_map ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T = 0 :=
  numerator_kills_of_inftySlice_zero
    ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
    (infiniteTailNumerator T) (infiniteTailNumerator_infty T)

/-- The zeroth finite slice of the tail numerator is the identity. -/
lemma infiniteTailNumerator_zero (T : LightProfinite) [Infinite T] :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) 0
      (infiniteTailNumerator T) = 𝟙 ((free ℤ).obj T.toCondensed) := by
  simpa [freeTailEndomorphism] using infiniteTailNumerator_slice T 0

/-- After every fixed finite projection of `T`, the finite slices of the tail numerator are
eventually zero. -/
lemma infiniteTailNumerator_eventually_freeProj_zero (T : LightProfinite) [Infinite T] (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
        (infiniteTailNumerator T) ≫ freeProj T k = 0 := by
  filter_upwards [freeTailEndomorphism_eventually_freeProj_zero T k] with n hn
  rw [infiniteTailNumerator_slice]
  exact hn

/-- Points in the successive finite quotients whose lifted differences generate the sequence map
`P ℤ ⟶ ℤ[T]`. -/
abbrev finiteDifferencePoint (T : LightProfinite) := Σ m : ℕ, T.component m

/-- A block enumeration of the finite sets `T.component m`, with the stage tending to infinity.
The surjectivity field records that every finite-stage point is eventually included. -/
structure NullFiniteDifferenceEnumeration (T : LightProfinite) where
  seq : ℕ → finiteDifferencePoint T
  stage_eventually_ge : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, k ≤ (seq n).1
  surjective : Function.Surjective seq
  seq_injective : Function.Injective seq

/-- The points in all stages below a fixed bound form a finite set. -/
lemma finiteDifferencePoint_initial_finite (T : LightProfinite) (k : ℕ) :
    Set.Finite {p : finiteDifferencePoint T | p.1 < k} := by
  classical
  letI (m : ℕ) : Fintype (T.component m) := Fintype.ofFinite _
  let s : Finset (finiteDifferencePoint T) :=
    (Finset.range k).sigma (fun m => (Finset.univ : Finset (T.component m)))
  have hs : {p : finiteDifferencePoint T | p.1 < k} = (s : Set (finiteDifferencePoint T)) := by
    ext p
    constructor
    · intro hp
      rcases p with ⟨m, a⟩
      simpa [s] using hp
    · intro hp
      rcases p with ⟨m, a⟩
      simpa [s] using hp
  rw [hs]
  exact s.finite_toSet

/-- The countable type of finite-difference points is equivalent to `ℕ` for an infinite test
object. -/
noncomputable def finiteDifferencePointEquivNat (T : LightProfinite) [Infinite T] :
    ℕ ≃ finiteDifferencePoint T := by
  classical
  haveI : Countable (finiteDifferencePoint T) := inferInstance
  haveI : Infinite (finiteDifferencePoint T) := by
    let t : T := Classical.arbitrary T
    let f : ℕ → finiteDifferencePoint T := fun n => ⟨n, T.proj n t⟩
    have hf : Function.Injective f := by
      intro a b h
      exact congrArg Sigma.fst h
    exact Infinite.of_injective f hf
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ finiteDifferencePoint T))

/-- Enumerate the countable union of the successive finite quotients in finite blocks, so that the
stage index tends to infinity. -/
lemma exists_nullFiniteDifferenceEnumeration (T : LightProfinite) [Infinite T] :
    Nonempty (NullFiniteDifferenceEnumeration T) := by
  classical
  let e : ℕ ≃ finiteDifferencePoint T := finiteDifferencePointEquivNat T
  refine ⟨⟨e, ?_, e.surjective, e.injective⟩⟩
  intro k
  have hbad : Set.Finite {n : ℕ | (e n).1 < k} := by
    have hinit := finiteDifferencePoint_initial_finite T k
    simpa [Set.preimage, e] using Set.Finite.preimage (Equiv.injective e).injOn hinit
  obtain ⟨N, hN⟩ := hbad.bddAbove
  refine Filter.eventually_atTop.2 ⟨N + 1, ?_⟩
  intro n hn
  by_contra hlt
  have hnmem : n ∈ {n : ℕ | (e n).1 < k} := by
    dsimp
    omega
  have := hN hnmem
  omega

/-- A chosen null enumeration of the points in the successive finite quotients of an infinite test
object. -/
noncomputable def nullFiniteDifferenceEnumeration (T : LightProfinite) [Infinite T] :
    NullFiniteDifferenceEnumeration T :=
  Classical.choice (exists_nullFiniteDifferenceEnumeration T)

/-- A chosen index at which a finite-stage point appears in the null enumeration. -/
noncomputable def finiteDifferenceIndex (T : LightProfinite) [Infinite T]
    (p : finiteDifferencePoint T) : ℕ :=
  ((nullFiniteDifferenceEnumeration T).surjective p).choose

/-- The chosen index really enumerates the requested finite-stage point. -/
lemma nullFiniteDifferenceEnumeration_seq_index (T : LightProfinite) [Infinite T]
    (p : finiteDifferencePoint T) :
    (nullFiniteDifferenceEnumeration T).seq (finiteDifferenceIndex T p) = p :=
  ((nullFiniteDifferenceEnumeration T).surjective p).choose_spec

/-- Looking up the index of an already enumerated finite-stage point gives the original index. -/
lemma finiteDifferenceIndex_seq (T : LightProfinite) [Infinite T] (i : ℕ) :
    finiteDifferenceIndex T ((nullFiniteDifferenceEnumeration T).seq i) = i :=
  (nullFiniteDifferenceEnumeration T).seq_injective
    (nullFiniteDifferenceEnumeration_seq_index T ((nullFiniteDifferenceEnumeration T).seq i))

/-- The free point-map associated to a point in a finite stage.  Stage `0` contributes the
initial finite approximation; stage `m+1` contributes the difference between adjacent chosen
finite-stage sections. -/
noncomputable def finiteDifferenceValue (T : LightProfinite) :
    (m : ℕ) → T.component m →
      ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
        (free ℤ).obj T.toCondensed)
  | 0, a => freePointMap T (LightProfinite.projSection T 0 a)
  | m + 1, a =>
      freePointMap T (LightProfinite.projSection T (m + 1) a) -
        freePointMap T (LightProfinite.projSection T m (T.transitionMap m a))

/-- A positive-stage finite difference vanishes after projection to every strictly earlier finite
quotient. -/
lemma finiteDifferenceValue_comp_freeProj_zero (T : LightProfinite) {k m : ℕ} (h : k < m)
    (a : T.component m) :
    finiteDifferenceValue T m a ≫ freeProj T k = 0 := by
  cases m with
  | zero => omega
  | succ m =>
      have hle : k ≤ m := by omega
      dsimp [finiteDifferenceValue]
      rw [Preadditive.sub_comp]
      rw [freePointMap_comp_freeProj]
      rw [freePointMap_comp_freeProj]
      have h₁ : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.transitionMapLE (show k ≤ m + 1 by omega) a := by
        have hmap := congrArg (fun f : T.component (m + 1) ⟶ T.component k => f a)
          (LightProfinite.projSection_proj_le T (show k ≤ m + 1 by omega))
        simpa using hmap
      have h₂ : T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) =
          T.transitionMapLE hle (T.transitionMap m a) := by
        have hmap := congrArg
          (fun f : T.component m ⟶ T.component k => f (T.transitionMap m a))
          (LightProfinite.projSection_proj_le T hle)
        simpa using hmap
      have htrans : T.transitionMap m ≫ T.transitionMapLE hle =
          T.transitionMapLE (show k ≤ m + 1 by omega) := by
        change T.diagram.map ⟨homOfLE (Nat.le_succ m)⟩ ≫ T.diagram.map ⟨homOfLE hle⟩ =
          T.diagram.map ⟨homOfLE (show k ≤ m + 1 by omega)⟩
        rw [← T.diagram.map_comp]
        congr 1
      have hpts : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) := by
        rw [h₁, h₂]
        change T.transitionMapLE (show k ≤ m + 1 by omega) a =
          (T.transitionMap m ≫ T.transitionMapLE hle) a
        rw [htrans]
      have hmaps := congrArg (freePointMap (T.component k)) hpts
      rw [hmaps]
      change freePointMap (T.component k)
            (T.proj k (LightProfinite.projSection T m (T.transitionMap m a))) -
          freePointMap (T.component k)
            (T.proj k (LightProfinite.projSection T m (T.transitionMap m a))) = 0
      abel

/-- The `n`th finite value of the null sequence defining the map `P ℤ ⟶ ℤ[T]`, obtained by
enumerating the successive finite-stage differences of the chosen AsLimit approximation of `T`. -/
noncomputable def infinitePToFreeFiniteValue (T : LightProfinite) [Infinite T] (n : ℕ) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  finiteDifferenceValue T ((nullFiniteDifferenceEnumeration T).seq n).1
    ((nullFiniteDifferenceEnumeration T).seq n).2

/-- Looking up a finite-stage point and then reading the corresponding finite value returns the
finite-stage difference attached to that point. -/
lemma infinitePToFreeFiniteValue_index (T : LightProfinite) [Infinite T] (m : ℕ)
    (a : T.component m) :
    infinitePToFreeFiniteValue T (finiteDifferenceIndex T ⟨m, a⟩) =
      finiteDifferenceValue T m a := by
  dsimp [infinitePToFreeFiniteValue]
  rw [nullFiniteDifferenceEnumeration_seq_index]

/-- The chosen finite values form a null sequence after every finite quotient of `T`. -/
lemma infinitePToFreeFiniteValue_eventually_freeProj_zero (T : LightProfinite) [Infinite T]
    (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, infinitePToFreeFiniteValue T n ≫ freeProj T k = 0 := by
  filter_upwards [(nullFiniteDifferenceEnumeration T).stage_eventually_ge (k + 1)] with n hn
  exact finiteDifferenceValue_comp_freeProj_zero T (by omega)
    ((nullFiniteDifferenceEnumeration T).seq n).2

/-- A null sequence of point-valued sections of `ℤ[T]` gives a section over `ℕ∪∞` with value
zero at `∞`.  This is reduced to the corresponding null-sequence bridge for endomorphisms by
choosing one point of `T` and splitting the map `ℤ[T] → ℤ[*]`. -/
lemma exists_freeElementOverNinf_of_eventually_freeProj_zero
    (T : LightProfinite) [Nonempty T]
    (u : ℕ → ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
      (free ℤ).obj T.toCondensed))
    (hu : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, u n ≫ freeProj T k = 0) :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints (LightProfinite.of PUnit.{1})
          ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op x) = u n) ∧
      (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ι.op x) = 0 := by
  let t0 : T := Classical.choice inferInstance
  let q : (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed :=
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T)
  let v : ℕ → ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed) := fun n => q ≫ u n
  have hv : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, v n ≫ freeProj T k = 0 := by
    intro k
    filter_upwards [hu k] with n hn
    dsimp [v]
    rw [Category.assoc, hn]
    simp
  let X := freeSectionOverNinfOfNullSequence T v hv
  let x : ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩ :=
    ((free ℤ).obj T.toCondensed).obj.map (ninfPointSection T t0).op X
  refine ⟨x, ?_, ?_⟩
  · intro n
    dsimp [x]
    rw [← Functor.map_comp_apply (((free ℤ).obj T.toCondensed).obj)
      (ninfPointSection T t0).op (natPoint n).op X]
    change (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ((natPoint n ≫ ninfPointSection T t0).op) X) =
      u n
    rw [natPoint_comp_ninfPointSection]
    rw [← freeHomEquivPoints_symm_map]
    rw [Functor.map_comp]
    rw [Functor.map_comp]
    change freePointMap T t0 ≫
        (((free ℤ).map (lightProfiniteToLightCondSet.map (finiteTensorPoint T n))) ≫
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
            ((free ℤ).obj T.toCondensed)).symm X) = u n
    rw [freeHomEquivPoints_symm_map]
    rw [freeSectionOverNinfOfNullSequence_finite]
    dsimp [v, q]
    change (freePointMap T t0 ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T)) ≫
      u n = u n
    rw [freePointMap_comp_toPointMap]
    change (𝟙 ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed)) ≫ u n = u n
    simp
  · dsimp [x]
    rw [← Functor.map_comp_apply (((free ℤ).obj T.toCondensed).obj)
      (ninfPointSection T t0).op ι.op X]
    change (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ((ι ≫ ninfPointSection T t0).op) X) = 0
    rw [iota_comp_ninfPointSection]
    rw [← freeHomEquivPoints_symm_map]
    rw [Functor.map_comp]
    rw [Functor.map_comp]
    change freePointMap T t0 ≫
        (((free ℤ).map (lightProfiniteToLightCondSet.map (inftyTensorPoint T))) ≫
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
            ((free ℤ).obj T.toCondensed)).symm X) = 0
    rw [freeHomEquivPoints_symm_map]
    rw [freeSectionOverNinfOfNullSequence_infty]
    simp

/-- The finite values `infinitePToFreeFiniteValue` form a null sequence, hence give a section over
`ℕ∪∞` with value zero at `∞`. -/
lemma exists_infinitePToFreeElement (T : LightProfinite) [Infinite T] :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints (LightProfinite.of PUnit.{1})
          ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op x) =
            infinitePToFreeFiniteValue T n) ∧
      (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ι.op x) = 0 :=
  exists_freeElementOverNinf_of_eventually_freeProj_zero T (infinitePToFreeFiniteValue T)
    (infinitePToFreeFiniteValue_eventually_freeProj_zero T)

/-- The section of `ℤ[T]` over `ℕ∪∞` whose finite values enumerate the successive finite-stage
differences and whose `∞` value is zero. -/
noncomputable def infinitePToFreeElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩ :=
  (exists_infinitePToFreeElement T).choose

/-- Restricting `infinitePToFreeElement` to the finite point `n` gives the prescribed finite
value. -/
lemma infinitePToFreeElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op (infinitePToFreeElement T)) =
        infinitePToFreeFiniteValue T n :=
  ((exists_infinitePToFreeElement T).choose_spec).1 n

/-- Restricting `infinitePToFreeElement` to `∞` gives zero. -/
lemma infinitePToFreeElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map ι.op (infinitePToFreeElement T)) = 0 :=
  ((exists_infinitePToFreeElement T).choose_spec).2

/-- The numerator of the map from the sequence object to the free object on `T`. -/
noncomputable def infinitePToFreeNumerator (T : LightProfinite) [Infinite T] :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  (freeHomEquivPoints (ℕ∪{∞}) ((free ℤ).obj T.toCondensed)).symm
    (infinitePToFreeElement T)

/-- The finite values of the numerator of `infinitePToFree` are the prescribed finite-stage
differences. -/
lemma infinitePToFreeNumerator_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    freeNatValue ((free ℤ).obj T.toCondensed) n (infinitePToFreeNumerator T) =
      infinitePToFreeFiniteValue T n := by
  dsimp [infinitePToFreeNumerator]
  rw [freeNatValue_of_freeElement]
  exact infinitePToFreeElement_finite T n

/-- The numerator of `infinitePToFree` is zero at `∞`. -/
lemma infinitePToFreeNumerator_infty (T : LightProfinite) [Infinite T] :
    freeInftyValue ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T) = 0 := by
  dsimp [infinitePToFreeNumerator]
  exact freeInftyValue_zero_of_element_infty ((free ℤ).obj T.toCondensed)
    (infinitePToFreeElement T) (infinitePToFreeElement_infty T)

/-- The numerator of `infinitePToFree` kills the basepoint summand. -/
lemma infinitePToFreeNumerator_kills (T : LightProfinite) [Infinite T] :
    P_map ℤ ≫ infinitePToFreeNumerator T = 0 :=
  freeNumerator_kills_of_inftyValue_zero ((free ℤ).obj T.toCondensed)
    (infinitePToFreeNumerator T) (infinitePToFreeNumerator_infty T)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma P_proj_comp_P_homMk (A : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ A) (hf : P_map ℤ ≫ f = 0) :
    P_proj ℤ ≫ P_homMk ℤ A f hf = f := by
  change cokernel.π (P_map ℤ) ≫ cokernel.desc (P_map ℤ) f hf = f
  exact cokernel.π_desc (P_map ℤ) f hf

/-- The map from the sequence object `P ℤ` to the free object on `T` used in Lemma 3.3.2. -/
noncomputable def infinitePToFree (T : LightProfinite) [Infinite T] :
    P ℤ ⟶ (free ℤ).obj T.toCondensed :=
  P_homMk ℤ ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T)
    (infinitePToFreeNumerator_kills T)

/-- The basis element of `P ℤ` at coordinate `i`, followed by `infinitePToFree`, is the chosen
finite-stage value at `i`. -/
lemma pBasis_comp_infinitePToFree (T : LightProfinite) [Infinite T] (i : ℕ) :
    pBasis i ≫ infinitePToFree T = freePointIsoUnit.inv ≫ infinitePToFreeFiniteValue T i := by
  dsimp [pBasis, infinitePToFree]
  rw [Category.assoc]
  rw [P_proj_comp_P_homMk]
  dsimp [freeNatBasis]
  rw [Category.assoc]
  change freePointIsoUnit.inv ≫
      freeNatValue ((free ℤ).obj T.toCondensed) i (infinitePToFreeNumerator T) =
    freePointIsoUnit.inv ≫ infinitePToFreeFiniteValue T i
  rw [infinitePToFreeNumerator_finite]

/-- The tail endomorphisms in Lemma 3.3.2, packaged as a map out of `P ℤ ⊗ ℤ[T]`. -/
noncomputable def infiniteTailMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  pTensorDesc ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
    (infiniteTailNumerator T) (infiniteTailNumerator_kills T)

/-- The locally constant finite-stage index map sending a point of `T.component n` to the place
where it appears in the null enumeration of finite-stage points. -/
noncomputable def finiteDifferenceIndexMap (T : LightProfinite) [Infinite T] (n : ℕ) :
    T.component n ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun a => (finiteDifferenceIndex T ⟨n, a⟩ : ℕ∪{∞}),
    continuous_of_discreteTopology⟩

@[simp]
lemma finiteDifferenceIndexMap_apply (T : LightProfinite) [Infinite T] (n : ℕ)
    (a : T.component n) :
    finiteDifferenceIndexMap T n a =
      (finiteDifferenceIndex T ⟨n, a⟩ : ℕ∪{∞}) := rfl

/-- The `n`th finite slice of the finite-difference factorization through `P ℤ`: project to the
`n`th finite quotient, look up the corresponding enumerating coordinate of `P`, and pass to the
quotient `P ℤ`. -/
noncomputable def infiniteDifferenceFiniteSlice (T : LightProfinite) [Infinite T] (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (T.proj n ≫ finiteDifferenceIndexMap T n) ≫
    P_proj ℤ

-- The finite natural generator, followed by `P_proj` and `infinitePToFree`, gives the
-- corresponding finite value in the chosen null sequence.
set_option backward.isDefEq.respectTransparency false in
lemma freeNatMap_comp_infinitePToFree (T : LightProfinite) [Infinite T] (i : ℕ) :
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint i)) ≫ P_proj ℤ ≫
      infinitePToFree T = infinitePToFreeFiniteValue T i := by
  dsimp [infinitePToFree]
  rw [P_proj_comp_P_homMk]
  change freeNatValue ((free ℤ).obj T.toCondensed) i (infinitePToFreeNumerator T) =
    infinitePToFreeFiniteValue T i
  rw [infinitePToFreeNumerator_finite]

-- Precomposing the finite-difference slice with a point of `T` selects the corresponding
-- coordinate of `P ℤ`.
set_option backward.isDefEq.respectTransparency false in
lemma freePointMap_comp_infiniteDifferenceFiniteSlice (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ infiniteDifferenceFiniteSlice T n =
      (free ℤ).map (lightProfiniteToLightCondSet.map
        (natPoint (finiteDifferenceIndex T ⟨n, T.proj n t⟩))) ≫ P_proj ℤ := by
  dsimp [freePointMap, infiniteDifferenceFiniteSlice]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t) ≫
      ((lightProfiniteToLightCondSet ⋙ free ℤ).map
        (T.proj n ≫ finiteDifferenceIndexMap T n) ≫ P_proj ℤ) =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (natPoint (finiteDifferenceIndex T ⟨n, T.proj n t⟩)) ≫ P_proj ℤ
  rw [← Category.assoc]
  rw [← Functor.map_comp]
  congr 1

/-- Pointwise, the finite-difference slice followed by `infinitePToFree` is the finite-stage
value indexed by the point's finite projection. -/
lemma freePointMap_comp_infiniteDifferenceFiniteSlice_comp (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T =
      finiteDifferenceValue T n (T.proj n t) := by
  rw [← Category.assoc]
  rw [freePointMap_comp_infiniteDifferenceFiniteSlice]
  rw [Category.assoc]
  rw [freeNatMap_comp_infinitePToFree]
  rw [infinitePToFreeFiniteValue_index]

lemma freePointMap_comp_freeFiniteApproxRetraction (T : LightProfinite) (n : ℕ) (t : T) :
    freePointMap T t ≫ freeFiniteApproxRetraction T n =
      freePointMap T (LightProfinite.finiteApproxRetraction T n t) := by
  exact freePointMap_comp T T (LightProfinite.finiteApproxRetraction T n) t

@[simp]
lemma finiteApproxRetraction_apply (T : LightProfinite) (n : ℕ) (t : T) :
    LightProfinite.finiteApproxRetraction T n t = LightProfinite.projSection T n (T.proj n t) :=
  rfl

/-- The finite-stage value at the `n`th projection of a point is the pointwise value of the
finite difference of tail endomorphisms. -/
lemma finiteDifferenceValue_eq_point_tail_diff (T : LightProfinite) (n : ℕ) (t : T) :
    finiteDifferenceValue T n (T.proj n t) =
      freePointMap T t ≫ (freeTailEndomorphism T n - freeTailEndomorphism T (n + 1)) := by
  cases n with
  | zero =>
      dsimp [finiteDifferenceValue, freeTailEndomorphism]
      change freePointMap T (LightProfinite.projSection T 0 (T.proj 0 t)) =
        freePointMap T t - (freePointMap T t -
          freePointMap T t ≫ freeFiniteApproxRetraction T 0)
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [finiteApproxRetraction_apply]
      abel
  | succ m =>
      dsimp [finiteDifferenceValue, freeTailEndomorphism]
      change freePointMap T (LightProfinite.projSection T (m + 1) (T.proj (m + 1) t)) -
          freePointMap T (LightProfinite.projSection T m (T.transitionMap m (T.proj (m + 1) t))) =
        (freePointMap T t - freePointMap T t ≫ freeFiniteApproxRetraction T m) -
          (freePointMap T t - freePointMap T t ≫ freeFiniteApproxRetraction T (m + 1))
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [finiteApproxRetraction_apply]
      rw [finiteApproxRetraction_apply]
      have hproj : T.proj m t = T.transitionMap m (T.proj (m + 1) t) := by
        have hmap := congrArg (fun f : T ⟶ T.component m => f t)
          (T.proj_comp_transitionMap m)
        simpa using hmap.symm
      rw [hproj]
      abel

/-- Pointwise form of the finite-difference factorization. -/
lemma infiniteDifferenceFiniteSlice_comp_pointwise (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ (infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T) =
      freePointMap T t ≫ (freeTailEndomorphism T n - freeTailEndomorphism T (n + 1)) := by
  rw [freePointMap_comp_infiniteDifferenceFiniteSlice_comp]
  rw [finiteDifferenceValue_eq_point_tail_diff]

/-- Each finite difference of tail endomorphisms factors through the chosen map
`infinitePToFree`. -/
lemma infiniteDifferenceFiniteSlice_comp (T : LightProfinite) [Infinite T] (n : ℕ) :
    infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T =
      freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  apply freeTarget_hom_ext_of_points
  intro t
  exact infiniteDifferenceFiniteSlice_comp_pointwise T n t

/-- The function on `(ℕ∪∞) × T` whose finite slices record the chosen finite-difference
coordinate and whose `∞` slice is `∞`. -/
noncomputable def finiteDifferenceIndexOverNinfFun (T : LightProfinite) [Infinite T] :
    ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) → ℕ∪{∞}
  | (∞, _) => ∞
  | (OnePoint.some n, t) => (finiteDifferenceIndex T ⟨n, T.proj n t⟩ : ℕ∪{∞})

/-- The finite fiber of the finite-difference index function is one finite slice of
`(ℕ∪∞) × T`, cut out by a finite quotient of `T`. -/
lemma finiteDifferenceIndexOverNinfFun_fiber_eq (T : LightProfinite) [Infinite T] (i : ℕ) :
    {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} =
    {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (((nullFiniteDifferenceEnumeration T).seq i).1 : ℕ∪{∞}) ∧
        T.proj (((nullFiniteDifferenceEnumeration T).seq i).1) x.2 =
          ((nullFiniteDifferenceEnumeration T).seq i).2} := by
  obtain ⟨m0, b0, hseqi⟩ : ∃ m0 : ℕ, ∃ b0 : T.component m0,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m0, b0⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m0, b0⟩
    exact ⟨m0, b0, rfl⟩
  ext x
  rcases x with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      simp [finiteDifferenceIndexOverNinfFun, hseqi]
  | coe n0 =>
      constructor
      · intro h
        have hidx : finiteDifferenceIndex T ⟨n0, T.proj n0 t⟩ = i := by
          simpa [finiteDifferenceIndexOverNinfFun] using h
        have hseq := nullFiniteDifferenceEnumeration_seq_index T ⟨n0, T.proj n0 t⟩
        rw [hidx, hseqi] at hseq
        cases hseq
        exact ⟨by simp [hseqi], by rw [hseqi]⟩
      · rintro ⟨hfst, hsnd⟩
        have hn : n0 = m0 := by
          simpa [hseqi] using hfst
        cases hn
        have hp : (⟨m0, T.proj m0 t⟩ : finiteDifferencePoint T) =
            (nullFiniteDifferenceEnumeration T).seq i := by
          have hsnd' : T.proj m0 t = b0 := by
            rw [hseqi] at hsnd
            exact hsnd
          rw [hseqi]
          simp [hsnd']
        have hidx := congrArg (finiteDifferenceIndex T) hp
        rw [finiteDifferenceIndex_seq] at hidx
        simpa [finiteDifferenceIndexOverNinfFun] using hidx

/-- Finite fibers of the finite-difference index function are open. -/
lemma isOpen_finiteDifferenceIndexOverNinfFun_fiber (T : LightProfinite) [Infinite T] (i : ℕ) :
    IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
  rw [finiteDifferenceIndexOverNinfFun_fiber_eq]
  obtain ⟨m, b, hseq⟩ : ∃ m : ℕ, ∃ b : T.component m,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m, b⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m, b⟩
    exact ⟨m, b, rfl⟩
  rw [hseq]
  have hfirst : IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (m : ℕ∪{∞})} := by
    have hopen : IsOpen ({(m : ℕ∪{∞})} : Set ℕ∪{∞}) := by
      simpa using (OnePoint.isOpen_image_coe (X := ℕ) (s := ({m} : Set ℕ))).2
        (isOpen_discrete _)
    simpa [IntProof.fstMap, Set.preimage, Set.setOf_eq_eq_singleton] using
      hopen.preimage (IntProof.fstMap T).continuous
  have hsecond : IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      T.proj m x.2 = b} := by
    letI : DiscreteTopology (T.component m) := Finite.instDiscreteTopology
    have hopen : IsOpen ({b} : Set (T.component m)) := isOpen_discrete _
    have hcont : Continuous
        (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) => T.proj m x.2) :=
      (T.proj m).hom.hom.continuous.comp (IntProof.sndMap T).continuous
    simpa [Set.preimage, Set.setOf_eq_eq_singleton] using hopen.preimage hcont
  simpa [Set.setOf_and] using hfirst.inter hsecond

/-- Finite fibers of the finite-difference index function are closed. -/
lemma isClosed_finiteDifferenceIndexOverNinfFun_fiber (T : LightProfinite) [Infinite T] (i : ℕ) :
    IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
  rw [finiteDifferenceIndexOverNinfFun_fiber_eq]
  obtain ⟨m, b, hseq⟩ : ∃ m : ℕ, ∃ b : T.component m,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m, b⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m, b⟩
    exact ⟨m, b, rfl⟩
  rw [hseq]
  have hfirst : IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (m : ℕ∪{∞})} := by
    have hclosed : IsClosed ({(m : ℕ∪{∞})} : Set ℕ∪{∞}) := isClosed_singleton
    simpa [IntProof.fstMap, Set.preimage, Set.setOf_eq_eq_singleton] using
      hclosed.preimage (IntProof.fstMap T).continuous
  have hsecond : IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      T.proj m x.2 = b} := by
    have hclosed : IsClosed ({b} : Set (T.component m)) := isClosed_singleton
    have hcont : Continuous
        (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) => T.proj m x.2) :=
      (T.proj m).hom.hom.continuous.comp (IntProof.sndMap T).continuous
    simpa [Set.preimage, Set.setOf_eq_eq_singleton] using hclosed.preimage hcont
  simpa [Set.setOf_and] using hfirst.inter hsecond

/-- The finite-difference index function is continuous.  This is the topological uniform-null part
of the AsLimit enumeration: finite output sets are hit by only finitely many finite input slices. -/
lemma continuous_finiteDifferenceIndexOverNinfFun (T : LightProfinite) [Infinite T] :
    Continuous (finiteDifferenceIndexOverNinfFun T) := by
  rw [continuous_def]
  intro s hs
  by_cases hinfty : (∞ : ℕ∪{∞}) ∈ s
  · let F : Set ℕ := (((↑) : ℕ → ℕ∪{∞}) ⁻¹' s)ᶜ
    have hcompact : IsCompact F := by
      dsimp [F]
      exact ((OnePoint.isOpen_iff_of_mem' (X := ℕ) hinfty).mp hs).1
    have hF : Set.Finite F := isCompact_iff_finite.mp hcompact
    have hpre : finiteDifferenceIndexOverNinfFun T ⁻¹' s =
        (⋃ i ∈ F, {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
          finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})})ᶜ := by
      ext x
      constructor
      · intro hx hmem
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem
        rcases hmem with ⟨i, hiF, hxi⟩
        have hi_not : (i : ℕ∪{∞}) ∉ s := hiF
        exact hi_not (hxi ▸ hx)
      · intro hx
        by_cases hfx : finiteDifferenceIndexOverNinfFun T x = (∞ : ℕ∪{∞})
        · change finiteDifferenceIndexOverNinfFun T x ∈ s
          rw [hfx]
          exact hinfty
        · rcases (OnePoint.ne_infty_iff_exists.mp hfx) with ⟨i, hi⟩
          have hnotF : i ∉ F := by
            intro hiF
            apply hx
            simp only [Set.mem_iUnion, Set.mem_setOf_eq]
            exact ⟨i, hiF, hi.symm⟩
          have hiA : i ∈ ((↑) : ℕ → ℕ∪{∞}) ⁻¹' s := by
            simpa [F] using hnotF
          change finiteDifferenceIndexOverNinfFun T x ∈ s
          rw [← hi]
          exact hiA
    rw [hpre]
    exact (hF.isClosed_biUnion fun i _ =>
      isClosed_finiteDifferenceIndexOverNinfFun_fiber T i).isOpen_compl
  · let A : Set ℕ := ((↑) : ℕ → ℕ∪{∞}) ⁻¹' s
    have hpre : finiteDifferenceIndexOverNinfFun T ⁻¹' s =
        ⋃ i ∈ A, {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
          finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
      ext x
      constructor
      · intro hx
        by_cases hfx : finiteDifferenceIndexOverNinfFun T x = (∞ : ℕ∪{∞})
        · change finiteDifferenceIndexOverNinfFun T x ∈ s at hx
          rw [hfx] at hx
          exact False.elim (hinfty hx)
        · rcases (OnePoint.ne_infty_iff_exists.mp hfx) with ⟨i, hi⟩
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          refine ⟨i, ?_, hi.symm⟩
          change finiteDifferenceIndexOverNinfFun T x ∈ s at hx
          rw [← hi] at hx
          exact hx
      · intro hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
        rcases hx with ⟨i, hiA, hxi⟩
        change finiteDifferenceIndexOverNinfFun T x ∈ s
        rw [hxi]
        exact hiA
    rw [hpre]
    exact isOpen_biUnion fun i _ => isOpen_finiteDifferenceIndexOverNinfFun_fiber T i

/-- The finite-difference index map `(ℕ∪∞) × T → ℕ∪∞`. -/
noncomputable def finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T] :
    ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨finiteDifferenceIndexOverNinfFun T,
    continuous_finiteDifferenceIndexOverNinfFun T⟩

@[simp]
lemma finiteDifferenceIndexOverNinf_finite (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    finiteDifferenceIndexOverNinf T ((n : ℕ∪{∞}), t) =
      (finiteDifferenceIndex T ⟨n, T.proj n t⟩ : ℕ∪{∞}) := rfl

@[simp]
lemma finiteDifferenceIndexOverNinf_infty (T : LightProfinite) [Infinite T] (t : T) :
    finiteDifferenceIndexOverNinf T ((∞ : ℕ∪{∞}), t) = (∞ : ℕ∪{∞}) := rfl

@[simp]
lemma finiteTensorPoint_comp_finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T]
    (n : ℕ) :
    finiteTensorPoint T n ≫ finiteDifferenceIndexOverNinf T =
      T.proj n ≫ finiteDifferenceIndexMap T n := by
  ext t
  rfl

/-- The constant map from `T` to the point `∞ ∈ ℕ∪∞`. -/
noncomputable def constInftyMap (T : LightProfinite) : T ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => (∞ : ℕ∪{∞}), continuous_const⟩

@[simp]
lemma inftyTensorPoint_comp_finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T] :
    inftyTensorPoint T ≫ finiteDifferenceIndexOverNinf T = constInftyMap T := by
  ext t
  rfl

lemma constInftyMap_eq (T : LightProfinite) : constInftyMap T = toPointMap T ≫ ι := by
  ext t
  rfl

/-- The constant-`∞` map dies after passing to `P ℤ`. -/
lemma free_constInftyMap_comp_P_proj (T : LightProfinite) :
    (free ℤ).map (lightProfiniteToLightCondSet.map (constInftyMap T)) ≫ P_proj ℤ = 0 := by
  rw [constInftyMap_eq]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T ≫ ι) ≫ P_proj ℤ = 0
  rw [Functor.map_comp]
  change ((lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ P_map ℤ) ≫
    P_proj ℤ = 0
  have hzero : P_map ℤ ≫ P_proj ℤ = 0 := by
    change P_map ℤ ≫ cokernel.π (P_map ℤ) = 0
    exact cokernel.condition (P_map ℤ)
  calc
    ((lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ P_map ℤ) ≫ P_proj ℤ
        = (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫
            (P_map ℤ ≫ P_proj ℤ) := by
          rw [Category.assoc]
    _ = (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ 0 := by
          exact congrArg
            (fun q => (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ q) hzero
    _ = 0 := by simp

/-- The finite-difference slices form a section of `P ℤ` over `(ℕ∪∞) × T` with zero `∞` slice,
assuming continuity of the finite-difference index map. -/
lemma exists_infiniteDifferenceElement (T : LightProfinite) [Infinite T] :
    ∃ x : (P ℤ).obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints T (P ℤ)).symm
          ((P ℤ).obj.map (finiteTensorPoint T n).op x) =
            infiniteDifferenceFiniteSlice T n) ∧
      (freeHomEquivPoints T (P ℤ)).symm
        ((P ℤ).obj.map (inftyTensorPoint T).op x) = 0 := by
  let f : (free ℤ).obj (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite).toCondensed) ⟶ P ℤ :=
    (free ℤ).map (lightProfiniteToLightCondSet.map (finiteDifferenceIndexOverNinf T)) ≫ P_proj ℤ
  let x := freeHomEquivPoints (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)) (P ℤ) f
  refine ⟨x, ?_, ?_⟩
  · intro n
    dsimp [x, f]
    rw [← freeHomEquivPoints_symm_map]
    rw [Equiv.symm_apply_apply]
    change (lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteTensorPoint T n) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteDifferenceIndexOverNinf T) ≫
          P_proj ℤ) = infiniteDifferenceFiniteSlice T n
    rw [← Category.assoc]
    rw [← Functor.map_comp]
    rw [finiteTensorPoint_comp_finiteDifferenceIndexOverNinf]
    rfl
  · dsimp [x, f]
    rw [← freeHomEquivPoints_symm_map]
    rw [Equiv.symm_apply_apply]
    change (lightProfiniteToLightCondSet ⋙ free ℤ).map (inftyTensorPoint T) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteDifferenceIndexOverNinf T) ≫
          P_proj ℤ) = 0
    rw [← Category.assoc]
    rw [← Functor.map_comp]
    rw [inftyTensorPoint_comp_finiteDifferenceIndexOverNinf]
    exact free_constInftyMap_comp_P_proj T

/-- The section of `P ℤ` over `(ℕ∪∞) × T` whose finite slices encode the finite-difference
factorization in Lemma 3.3.2 and whose `∞` slice is zero. -/
noncomputable def infiniteDifferenceElement (T : LightProfinite) [Infinite T] :
    (P ℤ).obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  (exists_infiniteDifferenceElement T).choose

/-- Restricting `infiniteDifferenceElement` to the finite slice `n` gives the prescribed
finite-difference factor. -/
lemma infiniteDifferenceElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints T (P ℤ)).symm
      ((P ℤ).obj.map (finiteTensorPoint T n).op (infiniteDifferenceElement T)) =
        infiniteDifferenceFiniteSlice T n :=
  ((exists_infiniteDifferenceElement T).choose_spec).1 n

/-- Restricting `infiniteDifferenceElement` to the `∞` slice gives zero. -/
lemma infiniteDifferenceElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints T (P ℤ)).symm
      ((P ℤ).obj.map (inftyTensorPoint T).op (infiniteDifferenceElement T)) = 0 :=
  ((exists_infiniteDifferenceElement T).choose_spec).2

/-- The numerator of the finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) (P ℤ)).symm
      (infiniteDifferenceElement T)

/-- Finite slices of the finite-difference numerator are the prescribed factors through `P ℤ`. -/
lemma infiniteDifferenceNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) (P ℤ) n (infiniteDifferenceNumerator T) =
      infiniteDifferenceFiniteSlice T n := by
  rw [infiniteDifferenceNumerator, numeratorSlice_of_freeTensorElement]
  exact infiniteDifferenceElement_finite T n

/-- The finite-difference numerator has zero `∞` slice. -/
lemma infiniteDifferenceNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) (P ℤ) (infiniteDifferenceNumerator T) = 0 := by
  rw [infiniteDifferenceNumerator, inftySlice_of_freeTensorElement]
  exact infiniteDifferenceElement_infty T

/-- The finite-difference numerator vanishes on the basepoint summand. -/
lemma infiniteDifferenceNumerator_kills (T : LightProfinite) [Infinite T] :
    (P_map ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteDifferenceNumerator T = 0 :=
  numerator_kills_of_inftySlice_zero ((free ℤ).obj T.toCondensed) (P ℤ)
    (infiniteDifferenceNumerator T) (infiniteDifferenceNumerator_infty T)

/-- The finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  pTensorDesc ((free ℤ).obj T.toCondensed) (P ℤ)
    (infiniteDifferenceNumerator T) (infiniteDifferenceNumerator_kills T)

/-- The section of the tail map in Lemma 3.3.2. -/
noncomputable def infiniteTailSection (T : LightProfinite) [Infinite T] :
    (free ℤ).obj T.toCondensed ⟶ P ℤ ⊗ (free ℤ).obj T.toCondensed :=
  tailSection T

/-- The finite slices of the shifted tail numerator are finite differences of tail
endomorphisms. -/
lemma shiftedTailNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (((oneMinusShift' ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T) =
    freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  rw [numeratorSlice_oneMinusShift']
  rw [infiniteTailNumerator_slice]
  rw [infiniteTailNumerator_slice]

/-- The `∞` slice of the shifted tail numerator is zero. -/
lemma shiftedTailNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (((oneMinusShift' ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T) = 0 := by
  rw [inftySlice_oneMinusShift']

/-- Finite slices commute with postcomposition by `infinitePToFree`. -/
lemma differenceNumerator_comp_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) =
    numeratorSlice ((free ℤ).obj T.toCondensed) (P ℤ) n (infiniteDifferenceNumerator T) ≫
      infinitePToFree T := by
  rw [numeratorSlice_comp]

/-- Finite slices of the postcomposed finite-difference numerator are the finite differences of
tail endomorphisms. -/
lemma differenceNumerator_comp_slice_eq (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) =
    freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  rw [differenceNumerator_comp_slice]
  rw [infiniteDifferenceNumerator_slice]
  rw [infiniteDifferenceFiniteSlice_comp]

/-- The `∞` slice of the finite-difference factorization is zero. -/
lemma differenceNumerator_comp_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) = 0 := by
  rw [inftySlice_comp]
  rw [infiniteDifferenceNumerator_infty]
  simp

/-- The numerator-level shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_numerator_comm (T : LightProfinite) [Infinite T] :
    (oneMinusShift' ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T =
      infiniteDifferenceNumerator T ≫ infinitePToFree T := by
  apply freeTarget_numerator_ext_of_slices T
  · intro n
    rw [shiftedTailNumerator_slice, differenceNumerator_comp_slice_eq]
  · rw [shiftedTailNumerator_infty, differenceNumerator_comp_infty]

/-- The shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_comm (T : LightProfinite) [Infinite T] :
    ((oneMinusShift ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailMap T =
      infiniteDifferenceMap T ≫ infinitePToFree T := by
  let M := (free ℤ).obj T.toCondensed
  haveI : Epi (P_proj ℤ ▷ M) := epi_P_proj_tensor M
  apply (cancel_epi (P_proj ℤ ▷ M)).1
  dsimp [infiniteTailMap, infiniteDifferenceMap, M]
  rw [← Category.assoc]
  rw [P_proj_tensor_oneMinusShift]
  rw [Category.assoc]
  rw [pTensorDesc_comp_proj]
  rw [← Category.assoc]
  rw [pTensorDesc_comp_proj]
  exact infiniteShiftRetract_numerator_comm T

/-- The tail-map section equation for Lemma 3.3.2. -/
lemma infiniteTailSection_fac (T : LightProfinite) [Infinite T] :
    infiniteTailSection T ≫ infiniteTailMap T = 𝟙 ((free ℤ).obj T.toCondensed) := by
  rw [infiniteTailSection, tailSection, infiniteTailMap]
  rw [pTensorDesc_slice]
  exact infiniteTailNumerator_zero T

/-- The concrete shift-retract data for Lemma 3.3.2, assembled from the named map and equation
obligations above. -/
noncomputable def solidifiedFreeShiftRetractData
    (T : LightProfinite) [Infinite T] :
    CategoryTheory.ShiftRetractData solidification where
  xObj := P ℤ ⊗ (free ℤ).obj T.toCondensed
  aObj := P ℤ
  bObj := (free ℤ).obj T.toCondensed
  s := (oneMinusShift ℤ) ▷ (free ℤ).obj T.toCondensed
  toB := infiniteTailMap T
  toA := infiniteDifferenceMap T
  g := infinitePToFree T
  comm := infiniteShiftRetract_comm T
  sect := infiniteTailSection T
  sect_fac := infiniteTailSection_fac T
  inverted := solidification_map_oneMinusShift_tensor_isIso ((free ℤ).obj T.toCondensed)

/-- For an infinite light profinite set, its solidified free representable is a retract of
`solidification.obj (P ℤ)`.  This is the heart-level retract form of Lemma 3.3.2. -/
noncomputable def solidifiedFreeRetractSolidPInfinite
    (T : LightProfinite) [Infinite T] :
    Retract
      (solidification.obj ((free ℤ).obj T.toCondensed))
      solidP :=
  (solidifiedFreeShiftRetractData T).retract

/-- Every solidified free representable is a retract of `solidification.obj (P ℤ)`, by first adding
an infinite coproduct summand. -/
noncomputable def solidifiedFreeRetractSolidP
    (S : LightProfinite) :
    Retract
      (solidification.obj ((free ℤ).obj S.toCondensed))
      solidP :=
  (freeRetractIntoInfinite S).map solidification |>.trans
    (solidifiedFreeRetractSolidPInfinite (infiniteEnvelope S))

/-- The solidification of `P ℤ` is a separator of solid abelian groups. -/
lemma solidP_isSeparator : IsSeparator solidP := by
  apply CategoryTheory.isSeparator_of_retracts_of_hom_ext
    (F := fun T : LightProfinite => solidification.obj ((free ℤ).obj T.toCondensed))
    (G := solidP)
  · intro X Y f g h
    exact solidifiedFree_hom_ext f g h
  · exact solidifiedFreeRetractSolidP

end ProjectiveGeneratorProof

/-- The countable product of copies of `ℤ` is projective in solid abelian groups. -/
instance solidProjectiveGenerator_projective : Projective solidProjectiveGenerator :=
  Projective.of_iso ProjectiveGeneratorProof.solidPIsoProduct
    (ProjectiveGeneratorProof.projective_solidP)

/-- The countable product of copies of `ℤ` is a separator/generator for solid abelian groups. -/
lemma solidProjectiveGenerator_isSeparator : IsSeparator solidProjectiveGenerator :=
  CategoryTheory.isSeparator_of_iso ProjectiveGeneratorProof.solidPIsoProduct
    ProjectiveGeneratorProof.solidP_isSeparator

end Solid
end LightCondensed
