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

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed

namespace CategoryTheory

/-- Separators are invariant under isomorphism. -/
lemma isSeparator_of_iso {C : Type*} [Category C]
    {G H : C} (e : G ≅ H) (hG : IsSeparator G) :
    IsSeparator H := by
  rw [isSeparator_def] at hG ⊢
  intro X Y f g hH
  apply hG f g
  intro k
  have hk := hH (e.inv ≫ k)
  have h := congrArg (fun t => e.hom ≫ t) hk
  simpa [Category.assoc] using h

/-- If a jointly separating family consists of retracts of `G`, then `G` is a separator. -/
lemma isSeparator_of_retracts_of_hom_ext
    {C : Type*} [Category C]
    {I : Type*} (F : I → C) (G : C)
    (hjoint : ∀ {X Y : C} (f g : X ⟶ Y),
      (∀ i (k : F i ⟶ X), k ≫ f = k ≫ g) → f = g)
    (r : ∀ i, Retract (F i) G) :
    IsSeparator G := by
  rw [isSeparator_def]
  intro X Y f g hG
  apply hjoint f g
  intro i k
  let ri := r i
  have hk := hG (ri.r ≫ k)
  have h := congrArg (fun t => ri.i ≫ t) hk
  simpa [Category.assoc, ri.retract] using h

/-- If a functor preserves a binary coproduct and the target has zero morphisms, the image of the
first summand is a retract of the image of the coproduct. -/
noncomputable def functor_obj_retract_coprod
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) (X Y : C)
    [HasBinaryCoproduct X Y] [HasBinaryCoproduct (F.obj X) (F.obj Y)]
    [PreservesColimit (pair X Y) F] :
    Retract (F.obj X) (F.obj (X ⨿ Y)) := by
  letI : IsIso (coprodComparison F X Y) := inferInstance
  refine {
    i := F.map (coprod.inl : X ⟶ X ⨿ Y)
    r := inv (coprodComparison F X Y) ≫ coprod.desc (𝟙 (F.obj X)) 0
    retract := ?_ }
  rw [map_inl_inv_coprodComparison_assoc, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
/-- If the tensor unit is projective, internal projectivity implies ordinary projectivity.
This packages the standard adjunction argument: maps out of `P` are global sections of
`P ⟶[C] -`, and `P ⟶[C] -` preserves epimorphisms by internal projectivity. -/
lemma projective_of_internallyProjective_of_projective_unit
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    (P : C) [Projective (𝟙_ C)] [InternallyProjective P] : Projective P where
  factors {E X} f e he := by
    letI : Epi e := he
    haveI : Epi ((ihom P).map e) := Functor.map_epi (ihom P) e
    let f' : 𝟙_ C ⟶ (ihom P).obj X := MonoidalClosed.curry ((ρ_ P).hom ≫ f)
    obtain ⟨g', hg'⟩ := Projective.factors f' ((ihom P).map e)
    refine ⟨(ρ_ P).inv ≫ MonoidalClosed.uncurry g', ?_⟩
    rw [Category.assoc]
    have huncurry := congrArg MonoidalClosed.uncurry hg'
    dsimp [f'] at huncurry
    rw [MonoidalClosed.uncurry_natural_right] at huncurry
    simpa using congrArg (fun k => (ρ_ P).inv ≫ k) huncurry

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

/-- The solidification of the sequence object `P ℤ`. -/
noncomputable abbrev solidP : Solid :=
  solidification.obj (P ℤ)

/-- The countable product of copies of `ℤ` in `Solid`. -/
noncomputable abbrev productInt : Solid :=
  solidProjectiveGenerator

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

/-- Obligation: for an infinite light profinite set, construct the map from the sequence object
`P ℤ` to the free object on `T` used in Lemma 3.3.2. -/
noncomputable def infinitePToFree (T : LightProfinite) [Infinite T] :
    P ℤ ⟶ (free ℤ).obj T.toCondensed := by
  sorry

/-- Obligation: the tail endomorphisms in Lemma 3.3.2, packaged as a map out of
`P ℤ ⊗ ℤ[T]`. -/
noncomputable def infiniteTailMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed := by
  sorry

/-- Obligation: the finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ := by
  sorry

/-- Obligation: the section of the tail map in Lemma 3.3.2. -/
noncomputable def infiniteTailSection (T : LightProfinite) [Infinite T] :
    (free ℤ).obj T.toCondensed ⟶ P ℤ ⊗ (free ℤ).obj T.toCondensed := by
  sorry

/-- Obligation: the shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_comm (T : LightProfinite) [Infinite T] :
    ((oneMinusShift ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailMap T =
      infiniteDifferenceMap T ≫ infinitePToFree T := by
  sorry

/-- Obligation: the tail-map section equation for Lemma 3.3.2. -/
lemma infiniteTailSection_fac (T : LightProfinite) [Infinite T] :
    infiniteTailSection T ≫ infiniteTailMap T = 𝟙 ((free ℤ).obj T.toCondensed) := by
  sorry

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
