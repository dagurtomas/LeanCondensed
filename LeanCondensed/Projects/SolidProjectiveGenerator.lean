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

/-- The `∞` value of a map out of the free object on `ℕ∪∞`. -/
noncomputable def freeInftyValue (N : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N) : 𝟙_ LightCondAb ⟶ N :=
  freeInftyBasis ≫ f

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

/-- Obligation: the section of `ℤ[T]` over `(ℕ∪∞) × T` whose finite slices are the tail
endomorphisms and whose `∞` slice is zero. -/
noncomputable def infiniteTailElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ := by
  sorry

/-- The numerator of the tail map, built from its section over `(ℕ∪∞) × T`. -/
noncomputable def infiniteTailNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
      ((free ℤ).obj T.toCondensed)).symm (infiniteTailElement T)

/-- Obligation: finite slices of the tail numerator are the prescribed tail endomorphisms. -/
lemma infiniteTailNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteTailNumerator T) = freeTailEndomorphism T n := by
  sorry

/-- Obligation: the `∞` slice of the tail numerator is zero. -/
lemma infiniteTailNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteTailNumerator T) = 0 := by
  sorry

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

/-- Obligation: the section of `ℤ[T]` over `ℕ∪∞` whose finite values enumerate the
successive finite-stage differences and whose `∞` value is zero. -/
noncomputable def infinitePToFreeElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩ := by
  sorry

/-- The numerator of the map from the sequence object to the free object on `T`. -/
noncomputable def infinitePToFreeNumerator (T : LightProfinite) [Infinite T] :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  (freeHomEquivPoints (ℕ∪{∞}) ((free ℤ).obj T.toCondensed)).symm
    (infinitePToFreeElement T)

/-- Obligation: the numerator of `infinitePToFree` is zero at `∞`. -/
lemma infinitePToFreeNumerator_infty (T : LightProfinite) [Infinite T] :
    freeInftyValue ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T) = 0 := by
  sorry

/-- The numerator of `infinitePToFree` kills the basepoint summand. -/
lemma infinitePToFreeNumerator_kills (T : LightProfinite) [Infinite T] :
    P_map ℤ ≫ infinitePToFreeNumerator T = 0 :=
  freeNumerator_kills_of_inftyValue_zero ((free ℤ).obj T.toCondensed)
    (infinitePToFreeNumerator T) (infinitePToFreeNumerator_infty T)

/-- The map from the sequence object `P ℤ` to the free object on `T` used in Lemma 3.3.2. -/
noncomputable def infinitePToFree (T : LightProfinite) [Infinite T] :
    P ℤ ⟶ (free ℤ).obj T.toCondensed :=
  P_homMk ℤ ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T)
    (infinitePToFreeNumerator_kills T)

/-- The tail endomorphisms in Lemma 3.3.2, packaged as a map out of `P ℤ ⊗ ℤ[T]`. -/
noncomputable def infiniteTailMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  pTensorDesc ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
    (infiniteTailNumerator T) (infiniteTailNumerator_kills T)

/-- Obligation: the section of `P ℤ` over `(ℕ∪∞) × T` whose finite slices encode the
finite-difference factorization in Lemma 3.3.2 and whose `∞` slice is zero. -/
noncomputable def infiniteDifferenceElement (T : LightProfinite) [Infinite T] :
    (P ℤ).obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ := by
  sorry

/-- The numerator of the finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) (P ℤ)).symm
      (infiniteDifferenceElement T)

/-- Obligation: the finite-difference numerator has zero `∞` slice. -/
lemma infiniteDifferenceNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) (P ℤ) (infiniteDifferenceNumerator T) = 0 := by
  sorry

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

/-- The `∞` slice of the finite-difference factorization is zero. -/
lemma differenceNumerator_comp_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) = 0 := by
  rw [inftySlice_comp]
  rw [infiniteDifferenceNumerator_infty]
  simp

/-- Obligation: the numerator-level shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_numerator_comm (T : LightProfinite) [Infinite T] :
    (oneMinusShift' ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T =
      infiniteDifferenceNumerator T ≫ infinitePToFree T := by
  sorry

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
