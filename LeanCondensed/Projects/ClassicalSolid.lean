/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Mathlib.Condensed.Light.Limits
public import LeanCondensed.Projects.FreeCondensed.ComparisonIso
public import LeanCondensed.Projects.SolidProjectiveGenerator
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Topology.Category.Profinite.Nobeling.Induction
public import Mathlib.Topology.Category.LightProfinite.Extend

/-!
# The classical definition of solid light condensed abelian groups

This file compares the definition of solidity in `LightCondensed.Solid.isSolid` with the
light analogue of the classical definition of solid abelian groups.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits LightProfinite MonoidalCategory MonoidalClosed

namespace LightCondensed
namespace Solid
namespace Classical

/-- The internal dual of a light condensed abelian group with respect to the discrete integer
object. -/
abbrev internalDual (X : LightCondAb) : LightCondAb :=
  (ihom X).obj IntProof.Zdisc

/-- The double internal dual of a light condensed abelian group with respect to the discrete
integer object. -/
abbrev doubleInternalDual (X : LightCondAb) : LightCondAb :=
  internalDual (internalDual X)

/-- The morphism on double internal duals induced by a morphism `f : X ⟶ Y`. -/
def doubleInternalDualMap {X Y : LightCondAb} (f : X ⟶ Y) :
    doubleInternalDual X ⟶ doubleInternalDual Y :=
  (MonoidalClosed.pre ((MonoidalClosed.pre f).app IntProof.Zdisc)).app IntProof.Zdisc

@[simp]
lemma doubleInternalDualMap_id (X : LightCondAb) :
    doubleInternalDualMap (𝟙 X) = 𝟙 (doubleInternalDual X) := by
  dsimp [doubleInternalDualMap]
  simp

@[reassoc]
lemma doubleInternalDualMap_comp {X Y Z : LightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    doubleInternalDualMap (f ≫ g) =
      doubleInternalDualMap f ≫ doubleInternalDualMap g := by
  dsimp [doubleInternalDualMap]
  simp

/-- The canonical evaluation morphism from an object to its double internal dual. It is obtained
by braiding, evaluation, and currying. -/
def doubleDualEvaluation (X : LightCondAb) : X ⟶ doubleInternalDual X :=
  MonoidalClosed.curry
    ((β_ (internalDual X) X).hom ≫ (ihom.ev X).app IntProof.Zdisc)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical evaluation morphism to the double internal dual is natural. -/
lemma doubleDualEvaluation_naturality {X Y : LightCondAb} (f : X ⟶ Y) :
    doubleDualEvaluation X ≫ doubleInternalDualMap f = f ≫ doubleDualEvaluation Y := by
  apply MonoidalClosed.uncurry_injective
  dsimp [doubleDualEvaluation, doubleInternalDualMap]
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
  rw [BraidedCategory.braiding_naturality_right_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A retract of objects induces a retract of their double-dual evaluation arrows. -/
noncomputable def doubleDualEvaluationRetract {X Y : LightCondAb} (r : Retract X Y) :
    RetractArrow (doubleDualEvaluation X) (doubleDualEvaluation Y) where
  i := Arrow.homMk r.i (doubleInternalDualMap r.i) (doubleDualEvaluation_naturality r.i).symm
  r := Arrow.homMk r.r (doubleInternalDualMap r.r) (doubleDualEvaluation_naturality r.r).symm
  retract := by
    apply Arrow.hom_ext <;> dsimp
    · change r.i ≫ r.r = 𝟙 X
      exact r.retract
    · change doubleInternalDualMap r.i ≫ doubleInternalDualMap r.r =
        𝟙 (doubleInternalDual X)
      rw [← doubleInternalDualMap_comp, r.retract, doubleInternalDualMap_id]

/-- The double-dual model for `ℤ[S]□`. -/
abbrev doubleDualCompletedFree (S : LightProfinite) : LightCondAb :=
  doubleInternalDual ((LightCondensed.free ℤ).obj S.toCondensed)

/-- The evaluation map from `ℤ[S]` to its double-dual completion. -/
def doubleDualCompletionMap (S : LightProfinite) :
    (LightCondensed.free ℤ).obj S.toCondensed ⟶ doubleDualCompletedFree S :=
  doubleDualEvaluation _

/-- The map on double-dual completions induced by a map of light profinite sets. -/
def doubleDualCompletedFreeMap {S T : LightProfinite} (f : S ⟶ T) :
    doubleDualCompletedFree S ⟶ doubleDualCompletedFree T :=
  doubleInternalDualMap ((lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ).map f)

/-- Naturality of the evaluation map from a free object to its double internal dual. -/
lemma doubleDualCompletionMap_naturality {S T : LightProfinite} (f : S ⟶ T) :
    (lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ).map f ≫
        doubleDualCompletionMap T =
      doubleDualCompletionMap S ≫ doubleDualCompletedFreeMap f := by
  exact (doubleDualEvaluation_naturality
    ((lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ).map f)).symm

/-- The classical extension condition: every morphism `ℤ[S] ⟶ A` extends uniquely across the
canonical map `ℤ[S] ⟶ ℤ[S]□`, for every light profinite set `S`. -/
def doubleDualExtensionProperty : ObjectProperty LightCondAb :=
  fun A => ∀ S : LightProfinite,
    Function.Bijective
      (fun (g : doubleDualCompletedFree S ⟶ A) => doubleDualCompletionMap S ≫ g)

/-- The free light condensed abelian group functor on light profinite sets. -/
abbrev lightProfiniteFreeℤ : LightProfinite ⥤ LightCondAb :=
  lightProfiniteToLightCondSet ⋙ LightCondensed.free ℤ

/-- The free light condensed abelian group functor restricted to finite sets. -/
abbrev finiteFreeℤ : FintypeCat ⥤ LightCondAb :=
  FintypeCat.toLightProfinite ⋙ lightProfiniteFreeℤ

/-- The functor sending `S` to the double internal dual of `ℤ[S]`. -/
def doubleDualFree : LightProfinite ⥤ LightCondAb where
  obj S := doubleDualCompletedFree S
  map f := doubleDualCompletedFreeMap f
  map_id S := by
    change doubleInternalDualMap (lightProfiniteFreeℤ.map (𝟙 S)) = _
    rw [lightProfiniteFreeℤ.map_id, doubleInternalDualMap_id]
    rfl
  map_comp f g := by
    change doubleInternalDualMap (lightProfiniteFreeℤ.map (f ≫ g)) =
      doubleInternalDualMap (lightProfiniteFreeℤ.map f) ≫
        doubleInternalDualMap (lightProfiniteFreeℤ.map g)
    rw [lightProfiniteFreeℤ.map_comp, doubleInternalDualMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation into the double internal dual, as a natural transformation on light profinite
sets. -/
def doubleDualCompletion : lightProfiniteFreeℤ ⟶ doubleDualFree where
  app S := doubleDualEvaluation (lightProfiniteFreeℤ.obj S)
  naturality _ _ f := doubleDualCompletionMap_naturality f

/-- The structured-arrow diagram defining the pointwise right Kan extension has a limit.  The
standard sequential presentation of `S` is initial in its category of finite quotients. -/
noncomputable instance (S : LightProfinite) : HasLimit
    (StructuredArrow.proj S FintypeCat.toLightProfinite ⋙ finiteFreeℤ) := by
  letI : (LightProfinite.Extend.functor S.asLimitCone).Initial :=
    LightProfinite.Extend.functor_initial S.asLimitCone S.asLimit
  apply Functor.Initial.hasLimit_of_comp (LightProfinite.Extend.functor S.asLimitCone)

/-- The completed free light condensed abelian group functor, defined as the right Kan extension
of `finiteFreeℤ` along the inclusion of finite sets into light profinite sets. -/
def classicalCompletedFree : LightProfinite ⥤ LightCondAb :=
  Functor.rightKanExtension FintypeCat.toLightProfinite finiteFreeℤ

/-- The counit exhibiting `classicalCompletedFree` as a right Kan extension of `finiteFreeℤ`. -/
def classicalCompletedFreeCounit :
    FintypeCat.toLightProfinite ⋙ classicalCompletedFree ⟶ finiteFreeℤ :=
  Functor.rightKanExtensionCounit FintypeCat.toLightProfinite finiteFreeℤ

instance : classicalCompletedFree.IsRightKanExtension classicalCompletedFreeCounit := by
  dsimp only [classicalCompletedFreeCounit, classicalCompletedFree]
  infer_instance

/-- The right Kan extension defining `classicalCompletedFree` is pointwise. -/
def classicalCompletedFreeIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _
      classicalCompletedFreeCounit).IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

/-- The canonical map from the ordinary free functor to its right-Kan completed version. -/
def classicalCompletion : lightProfiniteFreeℤ ⟶ classicalCompletedFree :=
  classicalCompletedFree.liftOfIsRightKanExtension
    classicalCompletedFreeCounit _ (𝟙 finiteFreeℤ)

/-- The classical extension condition, formulated using the right-Kan completed free object:
every map `ℤ[S] ⟶ A` extends uniquely across the canonical completion map, for every light
profinite set `S`. -/
def classicalIsSolid : ObjectProperty LightCondAb :=
  fun A => ∀ S : LightProfinite,
    Function.Bijective
      (fun (g : classicalCompletedFree.obj S ⟶ A) => classicalCompletion.app S ≫ g)

/-- The finite-stage cone whose point is the right-Kan completed free object on `S`. -/
def classicalCompletedFreeSequentialCone (S : LightProfinite) :
    Cone (S.fintypeDiagram ⋙ finiteFreeℤ) :=
  ((Functor.RightExtension.mk _ classicalCompletedFreeCounit).coneAt S).whisker
    (LightProfinite.Extend.functor S.asLimitCone)

/-- The right-Kan completed free object on `S` is the inverse limit of the free objects on the
standard finite stages `S.component n`. -/
noncomputable def classicalCompletedFreeSequentialConeIsLimit (S : LightProfinite) :
    IsLimit (classicalCompletedFreeSequentialCone S) := by
  letI : (LightProfinite.Extend.functor S.asLimitCone).Initial :=
    LightProfinite.Extend.functor_initial S.asLimitCone S.asLimit
  exact (Functor.Initial.isLimitWhiskerEquiv
    (LightProfinite.Extend.functor S.asLimitCone)
      ((Functor.RightExtension.mk _ classicalCompletedFreeCounit).coneAt S)).symm
        (classicalCompletedFreeIsPointwiseRightKanExtension S)

/-- The canonical isomorphism from the right-Kan completed free object to the inverse limit of
the free objects on the standard finite stages of `S`. -/
noncomputable def classicalCompletedFreeIsoSequentialLimit (S : LightProfinite) :
    classicalCompletedFree.obj S ≅ limit (S.fintypeDiagram ⋙ finiteFreeℤ) :=
  (classicalCompletedFreeSequentialConeIsLimit S).conePointUniqueUpToIso
    (limit.isLimit _)

@[reassoc (attr := simp)]
lemma classicalCompletedFreeIsoSequentialLimit_hom_π (S : LightProfinite) (n : ℕ) :
    (classicalCompletedFreeIsoSequentialLimit S).hom ≫
        limit.π (S.fintypeDiagram ⋙ finiteFreeℤ) ⟨n⟩ =
      (classicalCompletedFreeSequentialCone S).π.app ⟨n⟩ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical completion map followed by the `n`th inverse-limit projection is the free map
induced by `S.proj n : S ⟶ S.component n`. -/
lemma classicalCompletion_comp_sequentialCone_π (S : LightProfinite) (n : ℕ) :
    classicalCompletion.app S ≫
        (classicalCompletedFreeSequentialCone S).π.app ⟨n⟩ =
      lightProfiniteFreeℤ.map (S.proj n) := by
  change classicalCompletion.app S ≫
      (classicalCompletedFree.map (S.proj n) ≫
        classicalCompletedFreeCounit.app (S.fintypeDiagram.obj ⟨n⟩)) = _
  rw [← Category.assoc, ← classicalCompletion.naturality]
  rw [Category.assoc]
  have hfac : classicalCompletion.app (S.diagram.obj ⟨n⟩) ≫
      classicalCompletedFreeCounit.app (S.fintypeDiagram.obj ⟨n⟩) = 𝟙 _ := by
    change (classicalCompletedFree.liftOfIsRightKanExtension
        classicalCompletedFreeCounit lightProfiniteFreeℤ (𝟙 finiteFreeℤ)).app
        (FintypeCat.toLightProfinite.obj (S.fintypeDiagram.obj ⟨n⟩)) ≫
        classicalCompletedFreeCounit.app (S.fintypeDiagram.obj ⟨n⟩) =
      𝟙 (finiteFreeℤ.obj (S.fintypeDiagram.obj ⟨n⟩))
    exact classicalCompletedFree.liftOfIsRightKanExtension_fac_app
      classicalCompletedFreeCounit lightProfiniteFreeℤ (𝟙 finiteFreeℤ)
        (S.fintypeDiagram.obj ⟨n⟩)
  rw [hfac, Category.comp_id]

@[reassoc]
lemma classicalCompletion_comp_sequentialLimit_π (S : LightProfinite) (n : ℕ) :
    classicalCompletion.app S ≫ (classicalCompletedFreeIsoSequentialLimit S).hom ≫
        limit.π (S.fintypeDiagram ⋙ finiteFreeℤ) ⟨n⟩ =
      lightProfiniteFreeℤ.map (S.proj n) := by
  rw [classicalCompletedFreeIsoSequentialLimit_hom_π]
  exact classicalCompletion_comp_sequentialCone_π S n

/-- Nöbeling's theorem for a light profinite set. -/
instance locallyConstantInt_free (S : LightProfinite) :
    Module.Free ℤ (LocallyConstant S ℤ) := by
  change Module.Free ℤ (LocallyConstant (lightToProfinite.obj S) ℤ)
  infer_instance

/-- Integer-valued locally constant functions on a light profinite set form a countable type. -/
instance locallyConstantInt_countable (S : LightProfinite) : Countable (LocallyConstant S ℤ) := by
  letI (n : ℕ) : Countable (LocallyConstant (S.component n) ℤ) :=
    Function.Injective.countable LocallyConstant.coe_injective
  refine @Function.Surjective.countable
    (Σ n : ℕ, LocallyConstant (S.component n) ℤ) _ ?_ ?_ ?_
  · infer_instance
  · exact fun a => a.2.comap (S.proj a.1).hom.hom
  · intro f
    obtain ⟨n, g, rfl⟩ := LightProfinite.exists_locallyConstant_factor_proj S f
    exact ⟨⟨n, g⟩, rfl⟩

/-- Currying identifies locally constant functions on a product with locally constant families
of locally constant functions when the first factor is compact. -/
noncomputable def locallyConstantCurryEquiv (S T : LightProfinite) :
    LocallyConstant (S ⊗ T : LightProfinite) ℤ ≃
      LocallyConstant T (LocallyConstant S ℤ) where
  toFun f :=
    { toFun := fun t =>
        { toFun := fun s => f (s, t)
          isLocallyConstant := f.isLocallyConstant.comp_continuous
            (continuous_id.prodMk continuous_const) }
      isLocallyConstant := by
        apply IsLocallyConstant.iff_eventually_eq _ |>.2
        intro t
        have hswap : IsLocallyConstant (fun p : T × S => f (p.2, p.1)) :=
          f.isLocallyConstant.comp_continuous (continuous_snd.prodMk continuous_fst)
        have hfixed : IsLocallyConstant (fun p : T × S => f (p.2, t)) :=
          (f.isLocallyConstant.comp_continuous
            (continuous_id.prodMk continuous_const)).comp_continuous continuous_snd
        have hev : ∀ᶠ t' in nhds t, ∀ s : S, f (s, t') = f (s, t) :=
          isCompact_univ.eventually_forall_of_forall_eventually
            (P := fun t' s => f (s, t') = f (s, t))
            (K := Set.univ) (fun s _ => by
              filter_upwards [hswap.eventually_eq (t, s), hfixed.eventually_eq (t, s)]
                with p hp hp' using hp.trans hp'.symm) |>.mono
              (fun _ h s => h s (Set.mem_univ s))
        filter_upwards [hev] with t' ht'
        apply LocallyConstant.ext
        intro s
        exact ht' s }
  invFun f :=
    { toFun := fun p => f p.2 p.1
      isLocallyConstant := by
        apply IsLocallyConstant.iff_exists_open _ |>.2
        rintro ⟨s, t⟩
        obtain ⟨U, hU, hsU, hUs⟩ := (f t).isLocallyConstant.exists_open s
        obtain ⟨V, hV, htV, hVt⟩ := f.isLocallyConstant.exists_open t
        refine ⟨U ×ˢ V, hU.prod hV, ⟨hsU, htV⟩, ?_⟩
        rintro ⟨s', t'⟩ ⟨hs', ht'⟩
        change f t' s' = f t s
        exact (congrArg (fun q : LocallyConstant S ℤ => q s') (hVt t' ht')).trans
          (hUs s' hs') }
  left_inv f := rfl
  right_inv f := rfl

/-- The linear form of `locallyConstantCurryEquiv`. -/
noncomputable def locallyConstantCurryLinearEquiv (S T : LightProfinite) :
    LocallyConstant (S ⊗ T : LightProfinite) ℤ ≃ₗ[ℤ]
      LocallyConstant T (LocallyConstant S ℤ) := by
  let e : LocallyConstant (S ⊗ T : LightProfinite) ℤ ≃+
      LocallyConstant T (LocallyConstant S ℤ) :=
    { locallyConstantCurryEquiv S T with map_add' := fun _ _ => rfl }
  exact e.toIntLinearEquiv

/-- The sectionwise description of the internal dual of `ℤ[S]`. -/
lemma ihomPoints_sub_int (A B : LightCondAb) (T : LightProfinite)
    (x y : ((ihom A).obj B).obj.obj ⟨T⟩) :
    (ihomPoints ℤ A B T).toFun (x - y) =
      (ihomPoints ℤ A B T).toFun x - (ihomPoints ℤ A B T).toFun y := by
  change MonoidalClosed.uncurry
      ((ProjectiveGeneratorProof.freeHomEquivPoints T ((ihom A).obj B)).symm (x - y)) = _
  have hfree :
      (ProjectiveGeneratorProof.freeHomEquivPoints T ((ihom A).obj B)).symm (x - y) =
        (ProjectiveGeneratorProof.freeHomEquivPoints T ((ihom A).obj B)).symm x -
          (ProjectiveGeneratorProof.freeHomEquivPoints T ((ihom A).obj B)).symm y := by
    apply (ProjectiveGeneratorProof.freeHomEquivPoints T ((ihom A).obj B)).injective
    rw [ProjectiveGeneratorProof.freeHomEquivPoints_sub]
    simp
  rw [hfree]
  exact Adjunction.homAddEquiv_symm_sub (ihom.adjunction A) _ _ _ _

/-- The sectionwise description of the internal dual of `ℤ[S]`. -/
noncomputable def internalDualFreeSectionsEquiv (S T : LightProfinite) :
    (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      LocallyConstant T (LocallyConstant S ℤ) := by
  let e₁ : (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (((free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed) ⟶ IntProof.Zdisc) :=
    AddEquiv.toIntLinearEquiv
      { ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T with
        map_add' := by
          intro x y
          rw [← sub_eq_iff_eq_add]
          calc
            _ = (ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T).toFun
                ((x + y) - y) := (ihomPoints_sub_int _ _ _ (x + y) y).symm
            _ = _ := by congr 2; abel }
  let e₂ : (((free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed) ⟶
      IntProof.Zdisc) ≃ₗ[ℤ] LocallyConstant (S ⊗ T : LightProfinite) ℤ :=
    AddEquiv.toIntLinearEquiv
      { IntProof.freeProductHomEquiv S T with
        map_add' := by
          intro f g
          apply LocallyConstant.ext
          intro x
          change IntProof.freeProductHomEquiv S T (f + g) x =
            IntProof.freeProductHomEquiv S T f x + IntProof.freeProductHomEquiv S T g x
          rw [← sub_eq_iff_eq_add]
          rw [← IntProof.freeProductHomEquiv_sub_apply S T (f + g) g x]
          congr 2
          abel }
  exact e₁.trans (e₂.trans (locallyConstantCurryLinearEquiv S T))

@[reassoc]
lemma freeTensorIsoInt_inv_naturality_right {S T' T : LightProfinite} (f : T' ⟶ T) :
    (IntProof.freeTensorIsoInt S T').inv ≫
        ((free ℤ).obj S.toCondensed ◁ (free ℤ).map (lightProfiniteToLightCondSet.map f)) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (𝟙 S ⊗ₘ f)) ≫
        (IntProof.freeTensorIsoInt S T).inv := by
  dsimp [IntProof.freeTensorIsoInt]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right]
  simp only [← Functor.map_comp_assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right]
  simp [MonoidalCategory.id_tensorHom]

lemma freeProductHomEquiv_precomp_right {S T' T : LightProfinite} (f : T' ⟶ T)
    (g : (free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed ⟶ IntProof.Zdisc) :
    IntProof.freeProductHomEquiv S T'
        (((free ℤ).obj S.toCondensed ◁
            (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ g) =
      (IntProof.freeProductHomEquiv S T g).comap (𝟙 S ⊗ₘ f).hom.hom := by
  dsimp [IntProof.freeProductHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  have hcomp : (IntProof.freeTensorIsoInt S T').inv ≫
        (((free ℤ).obj S.toCondensed ◁
          (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ g) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (𝟙 S ⊗ₘ f)) ≫
        ((IntProof.freeTensorIsoInt S T).inv ≫ g) := by
    rw [← Category.assoc, freeTensorIsoInt_inv_naturality_right, Category.assoc]
  rw [hcomp]
  rw [IntProof.freeHomDiscreteEquiv_map]

lemma discreteModuleSectionsEquiv_restrict {T T' : LightProfinite} (f : T' ⟶ T)
    (M : ModuleCat ℤ) (x : ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨T⟩) :
    ProjectiveGeneratorProof.discreteModuleSectionsEquiv T' M
        (((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.map f.op x) =
      (ProjectiveGeneratorProof.discreteModuleSectionsEquiv T M x).comap f.hom.hom := by
  dsimp [ProjectiveGeneratorProof.discreteModuleSectionsEquiv]
  exact LightCondMod.hom_naturality_apply ℤ
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M) f.op x

lemma internalDualFreeSectionsEquiv_restrict (S : LightProfinite)
    {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩) :
    internalDualFreeSectionsEquiv S T'
        ((internalDual ((free ℤ).obj S.toCondensed)).obj.map f.op x) =
      (internalDualFreeSectionsEquiv S T x).comap f.hom.hom := by
  let e := ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T
  have h₁ : ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T'
        ((internalDual ((free ℤ).obj S.toCondensed)).obj.map f.op x) =
      ((free ℤ).obj S.toCondensed ◁
        (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ e x := by
    apply (ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T').symm.injective
    rw [Equiv.symm_apply_apply]
    rw [ihomPoints_symm_comp]
    simp [e]
  apply LocallyConstant.ext
  intro t'
  apply LocallyConstant.ext
  intro s
  change IntProof.freeProductHomEquiv S T'
      (ihomPoints ℤ ((free ℤ).obj S.toCondensed) IntProof.Zdisc T'
        ((internalDual ((free ℤ).obj S.toCondensed)).obj.map f.op x)) (s, t') = _
  rw [h₁, freeProductHomEquiv_precomp_right]
  rfl

lemma internalDualFreeSectionsEquiv_map {S' S : LightProfinite} (f : S' ⟶ S)
    (T : LightProfinite)
    (x : (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩) :
    internalDualFreeSectionsEquiv S' T
        ((((MonoidalClosed.pre
          ((free ℤ).map (lightProfiniteToLightCondSet.map f))).app IntProof.Zdisc).hom.app
            ⟨T⟩) x) =
      (internalDualFreeSectionsEquiv S T x).map
        (fun g => g.comap f.hom.hom) := by
  apply LocallyConstant.ext
  intro t
  apply LocallyConstant.ext
  intro s
  change IntProof.freeProductHomEquiv S' T
      (ihomPoints ℤ ((free ℤ).obj S'.toCondensed) IntProof.Zdisc T
        ((((MonoidalClosed.pre
          ((free ℤ).map (lightProfiniteToLightCondSet.map f))).app IntProof.Zdisc).hom.app
            ⟨T⟩) x)) (s, t) = _
  rw [IntProof.ihomPoints_pre_app]
  rw [IntProof.freeProductHomEquiv_precomp_left]
  rfl

/-- The linear locally constant-function description of sections of a discrete module. -/
noncomputable def discreteModuleSectionsLinearEquiv (T : LightProfinite) (M : ModuleCat ℤ) :
    ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      LocallyConstant T M := by
  let e : ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨T⟩ ≃+
      LocallyConstant T M :=
    { ProjectiveGeneratorProof.discreteModuleSectionsEquiv T M with
      map_add' := by
        intro x y
        change (((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M).hom.app ⟨T⟩)
            (x + y) = _
        exact (((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M).hom.app
          ⟨T⟩).hom.map_add x y }
  exact e.toIntLinearEquiv

lemma discreteModuleSectionsLinearEquiv_map (S : LightProfinite) {M N : ModuleCat ℤ}
    (f : M ⟶ N)
    (x : ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨S⟩) :
    discreteModuleSectionsLinearEquiv S N
        (((LightCondensed.discrete (ModuleCat ℤ)).map f).hom.app ⟨S⟩ x) =
      (discreteModuleSectionsLinearEquiv S M x).map f :=
  ProjectiveGeneratorProof.discreteModuleSectionsEquiv_map S f x

/-- On sections, the internal dual of `ℤ[S]` is the discrete module of locally constant
integer-valued functions on `S`. -/
noncomputable def internalDualFreeDiscreteSectionsEquiv (S T : LightProfinite) :
    (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ (LocallyConstant S ℤ))).obj.obj ⟨T⟩ :=
  (internalDualFreeSectionsEquiv S T).trans
    (discreteModuleSectionsLinearEquiv T
      (ModuleCat.of ℤ (LocallyConstant S ℤ))).symm

lemma internalDualFreeDiscreteSectionsEquiv_restrict (S : LightProfinite)
    {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual ((free ℤ).obj S.toCondensed)).obj.obj ⟨T⟩) :
    internalDualFreeDiscreteSectionsEquiv S T'
        ((internalDual ((free ℤ).obj S.toCondensed)).obj.map f.op x) =
      ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ (LocallyConstant S ℤ))).obj.map f.op
          (internalDualFreeDiscreteSectionsEquiv S T x) := by
  apply (discreteModuleSectionsLinearEquiv T'
    (ModuleCat.of ℤ (LocallyConstant S ℤ))).injective
  dsimp [internalDualFreeDiscreteSectionsEquiv]
  rw [LinearEquiv.apply_symm_apply]
  dsimp [discreteModuleSectionsLinearEquiv]
  rw [discreteModuleSectionsEquiv_restrict]
  rw [Equiv.apply_symm_apply]
  exact internalDualFreeSectionsEquiv_restrict S f x

/-- The internal dual of the free object `ℤ[S]` is the discrete light condensed module of
locally constant integer-valued functions on `S`. -/
noncomputable def internalDualFreeIso (S : LightProfinite) :
    internalDual ((free ℤ).obj S.toCondensed) ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ (LocallyConstant S ℤ)) where
  hom := {
    hom := {
      app T := ModuleCat.ofHom
        (internalDualFreeDiscreteSectionsEquiv S T.unop).toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        exact internalDualFreeDiscreteSectionsEquiv_restrict S f.unop x } }
  inv := {
    hom := {
      app T := ModuleCat.ofHom
        (internalDualFreeDiscreteSectionsEquiv S T.unop).symm.toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        apply (internalDualFreeDiscreteSectionsEquiv S T'.unop).injective
        change internalDualFreeDiscreteSectionsEquiv S T'.unop
            ((internalDualFreeDiscreteSectionsEquiv S T'.unop).symm
              (((LightCondensed.discrete (ModuleCat ℤ)).obj
                (ModuleCat.of ℤ (LocallyConstant S ℤ))).obj.map f.unop.op x)) = _
        rw [LinearEquiv.apply_symm_apply]
        change ((LightCondensed.discrete (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ (LocallyConstant S ℤ))).obj.map f.unop.op x =
          internalDualFreeDiscreteSectionsEquiv S T'.unop
            ((internalDual ((free ℤ).obj S.toCondensed)).obj.map f.unop.op
              ((internalDualFreeDiscreteSectionsEquiv S T.unop).symm x))
        rw [internalDualFreeDiscreteSectionsEquiv_restrict]
        rw [LinearEquiv.apply_symm_apply] } }
  hom_inv_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualFreeDiscreteSectionsEquiv S T.unop).symm_apply_apply x
  inv_hom_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualFreeDiscreteSectionsEquiv S T.unop).apply_symm_apply x

/-- Evaluation at the unique point identifies a locally constant family on a point with its
value. -/
noncomputable def locallyConstantPointLinearEquiv (M : ModuleCat ℤ) :
    LocallyConstant (LightProfinite.of PUnit.{1}) M ≃ₗ[ℤ] M := by
  let e : LocallyConstant (LightProfinite.of PUnit.{1}) M ≃+ M :=
    { toFun := fun f => f PUnit.unit
      invFun := fun m => LocallyConstant.const _ m
      left_inv := by intro f; ext x; cases x; rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact e.toIntLinearEquiv

/-- The point-value equivalence for an internal Hom is linear. -/
noncomputable def ihomPointsLinearEquiv (A B : LightCondAb) (T : LightProfinite) :
    ((ihom A).obj B).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (A ⊗ (free ℤ).obj T.toCondensed ⟶ B) :=
  AddEquiv.toIntLinearEquiv
    { ihomPoints ℤ A B T with
      map_add' := by
        intro x y
        rw [← sub_eq_iff_eq_add]
        calc
          _ = (ihomPoints ℤ A B T).toFun ((x + y) - y) :=
            (ihomPoints_sub_int A B T (x + y) y).symm
          _ = _ := by congr 2; abel }

/-- Sections of the internal dual of a discrete module are linear maps from that module to
locally constant integer-valued functions. -/
noncomputable def internalDualDiscreteSectionsEquiv (M : ModuleCat ℤ)
    (T : LightProfinite) :
    (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (M →ₗ[ℤ] LocallyConstant T ℤ) := by
  let F := (free ℤ).obj T.toCondensed
  let D := (LightCondensed.discrete (ModuleCat ℤ)).obj M
  let e₁ := ihomPointsLinearEquiv D IntProof.Zdisc T
  let e₂ : (D ⊗ F ⟶ IntProof.Zdisc) ≃+ (F ⊗ D ⟶ IntProof.Zdisc) :=
    { toFun := fun g => (β_ D F).inv ≫ g
      invFun := fun g => (β_ D F).hom ≫ g
      left_inv := by
        intro g
        change (β_ D F).hom ≫ (β_ D F).inv ≫ g = g
        simp
      right_inv := by
        intro g
        change (β_ D F).inv ≫ (β_ D F).hom ≫ g = g
        simp
      map_add' := by intro f g; simp }
  let e₃ : (F ⊗ D ⟶ IntProof.Zdisc) ≃+ (D ⟶ internalDual F) :=
    { toFun := MonoidalClosed.curry
      invFun := MonoidalClosed.uncurry
      left_inv := MonoidalClosed.uncurry_curry
      right_inv := MonoidalClosed.curry_uncurry
      map_add' := by
        intro f g
        change (ihom.adjunction F).homEquiv D IntProof.Zdisc (f + g) = _
        exact Adjunction.homAddEquiv_add (ihom.adjunction F) D IntProof.Zdisc f g }
  letI : (LightCondensed.underlying (ModuleCat ℤ)).Additive :=
    { map_add := by intros; apply ModuleCat.hom_ext; rfl }
  letI : (LightCondensed.discrete (ModuleCat ℤ)).Additive :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).left_adjoint_additive
  let e₄ : (D ⟶ internalDual F) ≃+
      (M ⟶ (LightCondensed.underlying (ModuleCat ℤ)).obj (internalDual F)) :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homAddEquiv M (internalDual F)
  let e₅ : (LightCondensed.underlying (ModuleCat ℤ)).obj (internalDual F) ≃ₗ[ℤ]
      LocallyConstant T ℤ :=
    (internalDualFreeSectionsEquiv T (LightProfinite.of PUnit.{1})).trans
      (locallyConstantPointLinearEquiv (ModuleCat.of ℤ (LocallyConstant T ℤ)))
  let e₆ : (M ⟶ (LightCondensed.underlying (ModuleCat ℤ)).obj (internalDual F)) ≃+
      (M →ₗ[ℤ] LocallyConstant T ℤ) :=
    { toFun := fun g => e₅.toLinearMap.comp g.hom
      invFun := fun g => ModuleCat.ofHom (e₅.symm.toLinearMap.comp g)
      left_inv := by
        intro g
        apply ModuleCat.hom_ext
        ext m
        simp
      right_inv := by
        intro g
        ext m t
        exact LocallyConstant.congr_fun (e₅.apply_symm_apply (g m)) t
      map_add' := by intro g h; ext m; simp }
  let e : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.obj ⟨T⟩ ≃+
      (M →ₗ[ℤ] LocallyConstant T ℤ) :=
    e₁.toAddEquiv.trans (e₂.trans (e₃.trans
      (e₄.trans e₆)))
  let l : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.obj ⟨T⟩ →ₗ[ℤ]
      (M →ₗ[ℤ] LocallyConstant T ℤ) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by intro n x; exact map_intCast_smul e ℤ ℤ n x }
  exact LinearEquiv.ofBijective l e.bijective

lemma internalDualDiscreteSectionsEquiv_restrict (M : ModuleCat ℤ)
    {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.obj ⟨T⟩) :
    internalDualDiscreteSectionsEquiv M T'
        ((internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.map f.op x) =
      ({ toFun := fun g => g.comap f.hom.hom
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        LocallyConstant T ℤ →ₗ[ℤ] LocallyConstant T' ℤ).comp
          (internalDualDiscreteSectionsEquiv M T x) := by
  let D := (LightCondensed.discrete (ModuleCat ℤ)).obj M
  let q := ihomPoints ℤ D IntProof.Zdisc T x
  have h₁ : ihomPoints ℤ D IntProof.Zdisc T'
        ((internalDual D).obj.map f.op x) =
      (D ◁ (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ q := by
    apply (ihomPoints ℤ D IntProof.Zdisc T').symm.injective
    rw [Equiv.symm_apply_apply]
    rw [ihomPoints_symm_comp]
    simp [q]
  let ff := (free ℤ).map (lightProfiniteToLightCondSet.map f)
  have h₂ : MonoidalClosed.curry
        ((β_ D ((free ℤ).obj T'.toCondensed)).inv ≫ (D ◁ ff) ≫ q) =
      MonoidalClosed.curry ((β_ D ((free ℤ).obj T.toCondensed)).inv ≫ q) ≫
        (MonoidalClosed.pre ff).app IntProof.Zdisc := by
    rw [MonoidalClosed.curry_pre_app]
    congr 1
    exact (BraidedCategory.braiding_inv_naturality_left_assoc ff D q).symm
  have h₃ :
      ((ihom.adjunction ((free ℤ).obj T'.toCondensed)).homAddEquiv D IntProof.Zdisc)
          ((β_ D ((free ℤ).obj T'.toCondensed)).inv ≫ (D ◁ ff) ≫ q) =
        ((ihom.adjunction ((free ℤ).obj T.toCondensed)).homAddEquiv D IntProof.Zdisc)
            ((β_ D ((free ℤ).obj T.toCondensed)).inv ≫ q) ≫
          (MonoidalClosed.pre ff).app IntProof.Zdisc := by
    exact h₂
  let k : D ⟶ internalDual ((free ℤ).obj T.toCondensed) :=
    MonoidalClosed.curry ((β_ D ((free ℤ).obj T.toCondensed)).inv ≫ q)
  let d : internalDual ((free ℤ).obj T.toCondensed) ⟶
      internalDual ((free ℤ).obj T'.toCondensed) :=
    (MonoidalClosed.pre ff).app IntProof.Zdisc
  have h₄ :
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
        (internalDual ((free ℤ).obj T'.toCondensed))) (k ≫ d) =
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
        (internalDual ((free ℤ).obj T.toCondensed))) k ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map d :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv_naturality_right k d
  dsimp [internalDualDiscreteSectionsEquiv, ihomPointsLinearEquiv]
  rw [h₁]
  rw [h₂]
  rw [show ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
      (internalDual ((free ℤ).obj T'.toCondensed)))
        (MonoidalClosed.curry ((β_ D ((free ℤ).obj T.toCondensed)).inv ≫ q) ≫
          (MonoidalClosed.pre ff).app IntProof.Zdisc) =
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
        (internalDual ((free ℤ).obj T.toCondensed))) k ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map d by exact h₄]
  ext m t'
  let y : (internalDual ((free ℤ).obj T.toCondensed)).obj.obj
      ⟨LightProfinite.of PUnit.{1}⟩ :=
    (((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
      (internalDual ((free ℤ).obj T.toCondensed))) k).hom m
  change (internalDualFreeSectionsEquiv T' (LightProfinite.of PUnit.{1})
      ((d.hom.app ⟨LightProfinite.of PUnit.{1}⟩) y) PUnit.unit) t' =
    ((internalDualFreeSectionsEquiv T (LightProfinite.of PUnit.{1}) y PUnit.unit).comap
      f.hom.hom) t'
  have hmap := internalDualFreeSectionsEquiv_map f (LightProfinite.of PUnit.{1}) y
  exact LocallyConstant.congr_fun
    (congrArg (fun z : LocallyConstant (LightProfinite.of PUnit.{1})
      (LocallyConstant T' ℤ) => z PUnit.unit) hmap) t'

/-- An isomorphism of light condensed abelian groups induces a linear equivalence on sections. -/
noncomputable def isoSectionsLinearEquiv {A B : LightCondAb} (e : A ≅ B)
    (T : LightProfinite) :
    A.obj.obj ⟨T⟩ ≃ₗ[ℤ] B.obj.obj ⟨T⟩ where
  toFun x := e.hom.hom.app ⟨T⟩ x
  invFun x := e.inv.hom.app ⟨T⟩ x
  left_inv x := by
    change (e.hom ≫ e.inv).hom.app ⟨T⟩ x = x
    simp
  right_inv x := by
    change (e.inv ≫ e.hom).hom.app ⟨T⟩ x = x
    simp
  map_add' x y := (e.hom.hom.app ⟨T⟩).hom.map_add x y
  map_smul' n x := (e.hom.hom.app ⟨T⟩).hom.map_smul n x

/-- The module-valued presheaf of locally constant integer-valued functions. -/
abbrev locallyConstantIntModulePresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ :=
  (LightCondMod.LocallyConstant.functorToPresheaves ℤ).obj (ModuleCat.of ℤ ℤ)

set_option maxHeartbeats 800000 in
/-- The internal dual of a free object, contravariantly functorial in the light profinite set. -/
def internalDualFreeFunctor : LightProfiniteᵒᵖ ⥤ LightCondAb where
  obj S := internalDual (lightProfiniteFreeℤ.obj S.unop)
  map f := (MonoidalClosed.pre (lightProfiniteFreeℤ.map f.unop)).app IntProof.Zdisc
  map_id S := by
    change (MonoidalClosed.pre (lightProfiniteFreeℤ.map (𝟙 S.unop))).app
      IntProof.Zdisc = _
    rw [lightProfiniteFreeℤ.map_id]
    simp
  map_comp f g := by
    change (MonoidalClosed.pre (lightProfiniteFreeℤ.map (g.unop ≫ f.unop))).app
        IntProof.Zdisc = _
    rw [lightProfiniteFreeℤ.map_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The internal dual of `ℤ[S]`, naturally in `S`, is the discrete module of locally constant
integer-valued functions on `S`. -/
noncomputable def internalDualFreeNatIsoDiscrete :
    internalDualFreeFunctor ≅
      locallyConstantIntModulePresheaf ⋙ LightCondensed.discrete (ModuleCat ℤ) :=
  NatIso.ofComponents (fun S => internalDualFreeIso S.unop) (by
    intro S T f
    apply LightCondensed.hom_ext
    intro U
    ext x
    apply (discreteModuleSectionsLinearEquiv U.unop
      (ModuleCat.of ℤ (LocallyConstant T.unop ℤ))).injective
    change discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant T.unop ℤ))
          ((internalDualFreeIso T.unop).hom.hom.app U
            (((MonoidalClosed.pre (lightProfiniteFreeℤ.map f.unop)).app
              IntProof.Zdisc).hom.app U x)) =
      discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant T.unop ℤ))
          (((LightCondensed.discrete (ModuleCat ℤ)).map
            (locallyConstantIntModulePresheaf.map f)).hom.app U
              ((internalDualFreeIso S.unop).hom.hom.app U x))
    rw [show discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant T.unop ℤ))
          ((internalDualFreeIso T.unop).hom.hom.app U
            (((MonoidalClosed.pre (lightProfiniteFreeℤ.map f.unop)).app
              IntProof.Zdisc).hom.app U x)) =
      internalDualFreeSectionsEquiv T.unop U.unop
        (((MonoidalClosed.pre (lightProfiniteFreeℤ.map f.unop)).app
          IntProof.Zdisc).hom.app U x) by
      simp [internalDualFreeIso, internalDualFreeDiscreteSectionsEquiv]]
    let z := (internalDualFreeIso S.unop).hom.hom.app U x
    have hz : (discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant S.unop ℤ))) z =
      internalDualFreeSectionsEquiv S.unop U.unop x := by
      change (discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant S.unop ℤ)))
          (internalDualFreeDiscreteSectionsEquiv S.unop U.unop x) = _
      change (discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant S.unop ℤ)))
          ((discreteModuleSectionsLinearEquiv U.unop
            (ModuleCat.of ℤ (LocallyConstant S.unop ℤ))).symm
              (internalDualFreeSectionsEquiv S.unop U.unop x)) = _
      exact (discreteModuleSectionsLinearEquiv U.unop
        (ModuleCat.of ℤ (LocallyConstant S.unop ℤ))).apply_symm_apply _
    have hr := discreteModuleSectionsLinearEquiv_map U.unop
      (locallyConstantIntModulePresheaf.map f) z
    calc
      _ = (internalDualFreeSectionsEquiv S.unop U.unop x).map
          (fun g => g.comap f.unop.hom.hom) :=
        internalDualFreeSectionsEquiv_map f.unop U.unop x
      _ = (discreteModuleSectionsLinearEquiv U.unop
          (ModuleCat.of ℤ (LocallyConstant S.unop ℤ)) z).map
            (locallyConstantIntModulePresheaf.map f) := by
        rw [hz]
        rfl
      _ = _ := hr.symm)

@[simp]
lemma internalDualFreeNatIsoDiscrete_hom_app (S : LightProfiniteᵒᵖ) :
    internalDualFreeNatIsoDiscrete.hom.app S = (internalDualFreeIso S.unop).hom := rfl

@[simp]
lemma internalDualFreeNatIsoDiscrete_inv_app (S : LightProfiniteᵒᵖ) :
    internalDualFreeNatIsoDiscrete.inv.app S = (internalDualFreeIso S.unop).inv := rfl

/-- Replacing the first internal dual of `ℤ[S]` by its discrete locally-constant-function
description identifies the double dual with the dual of that discrete module. -/
noncomputable def doubleDualFreeIsoInternalDualDiscrete (S : LightProfinite) :
    doubleDualCompletedFree S ≅
      internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ (LocallyConstant S ℤ))) :=
  ((MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).mapIso
    (internalDualFreeIso S).op).symm

/-- The internal dual of the discrete module of locally constant integer-valued functions,
covariantly functorial in the light profinite set. -/
def lightProfiniteToDoubleOpposite : LightProfinite ⥤ LightProfiniteᵒᵖᵒᵖ where
  obj S := Opposite.op (Opposite.op S)
  map f := f.op.op
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma lightProfiniteToDoubleOpposite_map_unop_unop {S T : LightProfinite} (f : S ⟶ T) :
    (lightProfiniteToDoubleOpposite.map f).unop.unop = f := rfl

def internalDualDiscreteLocallyConstantFunctor : LightProfinite ⥤ LightCondAb :=
  lightProfiniteToDoubleOpposite ⋙
    (locallyConstantIntModulePresheaf ⋙
      LightCondensed.discrete (ModuleCat ℤ)).op ⋙
        MonoidalClosed.internalHom.flip.obj IntProof.Zdisc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The double dual of the free functor is naturally the internal dual of the discrete locally
constant-function module. -/
noncomputable def doubleDualFreeNatIsoInternalDualDiscrete :
    doubleDualFree ≅ internalDualDiscreteLocallyConstantFunctor :=
  NatIso.ofComponents doubleDualFreeIsoInternalDualDiscrete (by
    intro S T f
    let K := MonoidalClosed.internalHom.flip.obj IntProof.Zdisc
    have h := internalDualFreeNatIsoDiscrete.inv.naturality f.op
    have hop := congrArg Quiver.Hom.op h
    have hmap := congrArg K.map hop
    simpa [K, doubleDualFreeIsoInternalDualDiscrete, doubleDualFree,
      doubleDualCompletedFreeMap, doubleInternalDualMap,
      internalDualDiscreteLocallyConstantFunctor, internalDualFreeFunctor] using hmap.symm)

@[simp]
lemma doubleDualFreeNatIsoInternalDualDiscrete_hom_app (S : LightProfinite) :
    doubleDualFreeNatIsoInternalDualDiscrete.hom.app S =
      (doubleDualFreeIsoInternalDualDiscrete S).hom := rfl

@[simp]
lemma doubleDualFreeNatIsoInternalDualDiscrete_inv_app (S : LightProfinite) :
    doubleDualFreeNatIsoInternalDualDiscrete.inv.app S =
      (doubleDualFreeIsoInternalDualDiscrete S).inv := rfl

/-- Sections of the double dual of `ℤ[S]` are linear maps from the locally constant
integer-valued functions on `S` to those on the test object `T`. -/
noncomputable def doubleDualFreeSectionsEquiv (S T : LightProfinite) :
    (doubleDualCompletedFree S).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (LocallyConstant S ℤ →ₗ[ℤ] LocallyConstant T ℤ) :=
  (isoSectionsLinearEquiv (doubleDualFreeIsoInternalDualDiscrete S) T).trans
    (internalDualDiscreteSectionsEquiv
      (ModuleCat.of ℤ (LocallyConstant S ℤ)) T)

/-- Sections of an arbitrary product of copies of `Zdisc`, in coordinates. -/
noncomputable def piZdiscSectionsEquiv (I : Type) (T : LightProfinite) :
    (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (∀ _ : I, IntProof.Zdisc.obj.obj ⟨T⟩) := by
  let evT : Functor LightCondAb (ModuleCat ℤ) :=
    sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ) ⋙
      (evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj ⟨T⟩
  let e := PreservesProduct.iso evT (fun _ : I => IntProof.Zdisc) ≪≫
    ModuleCat.piIsoPi (fun _ : I => evT.obj IntProof.Zdisc)
  let coord : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ →
      (∀ _ : I, IntProof.Zdisc.obj.obj ⟨T⟩) :=
    fun x i => (Limits.Pi.π (fun _ : I => IntProof.Zdisc) i).hom.app ⟨T⟩ x
  have hcoord : ∀ x, e.hom x = coord x := by
    intro x
    ext i
    letI : Module ℤ (∀ _ : I, evT.obj IntProof.Zdisc) :=
      Pi.module I (fun _ : I => evT.obj IntProof.Zdisc) ℤ
    change (((PreservesProduct.iso evT (fun _ : I => IntProof.Zdisc)).hom ≫
      (ModuleCat.piIsoPi (fun _ : I => evT.obj IntProof.Zdisc)).hom) ≫ ModuleCat.ofHom
        (LinearMap.proj i : (∀ _ : I, evT.obj IntProof.Zdisc) →ₗ[ℤ]
          evT.obj IntProof.Zdisc)).hom x = _
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    change ((PreservesProduct.iso evT (fun _ : I => IntProof.Zdisc)).hom ≫
      Limits.Pi.π (fun _ : I => evT.obj IntProof.Zdisc) i).hom x = _
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
    rfl
  let a : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ ≃+
      (∀ _ : I, IntProof.Zdisc.obj.obj ⟨T⟩) :=
    { toFun := coord
      invFun := fun y => e.inv y
      left_inv := by
        intro x
        change e.inv (coord x) = x
        rw [← hcoord x]
        change (e.hom ≫ e.inv).hom x = x
        rw [e.hom_inv_id]
        rfl
      right_inv := by
        intro y
        change coord (e.inv y) = y
        rw [← hcoord (e.inv y)]
        change (e.inv ≫ e.hom).hom y = y
        rw [e.inv_hom_id]
        rfl
      map_add' := by
        intro x y
        ext i
        exact ((Limits.Pi.π (fun _ : I => IntProof.Zdisc) i).hom.app ⟨T⟩).hom.map_add x y }
  exact a.toIntLinearEquiv

@[simp]
lemma piZdiscSectionsEquiv_apply (I : Type) (T : LightProfinite)
    (x : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩) (i : I) :
    piZdiscSectionsEquiv I T x i =
      (Limits.Pi.π (fun _ : I => IntProof.Zdisc) i).hom.app ⟨T⟩ x := rfl

/-- Sections of a product of copies of `Zdisc` as families of locally constant functions. -/
noncomputable def piZdiscLocallyConstantSectionsEquiv (I : Type) (T : LightProfinite) :
    (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (∀ _ : I, LocallyConstant T ℤ) := by
  let e : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ ≃+
      (∀ _ : I, LocallyConstant T ℤ) :=
    (piZdiscSectionsEquiv I T).toAddEquiv.trans
      { toFun := fun x i => ProjectiveGeneratorProof.zdiscSectionsEquiv T (x i)
        invFun := fun x i => (ProjectiveGeneratorProof.zdiscSectionsEquiv T).symm (x i)
        left_inv := by
          intro x
          apply funext
          intro i
          exact Equiv.symm_apply_apply _ _
        right_inv := by
          intro x
          apply funext
          intro i
          exact Equiv.apply_symm_apply _ _
        map_add' := by
          intro x y
          apply funext
          intro i
          exact (ProjectiveGeneratorProof.zdiscSectionsLinearEquiv T).map_add (x i) (y i) }
  let l : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ →ₗ[ℤ]
      (∀ _ : I, LocallyConstant T ℤ) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by intro n x; exact map_intCast_smul e ℤ ℤ n x }
  exact LinearEquiv.ofBijective l e.bijective

lemma piZdiscLocallyConstantSectionsEquiv_restrict (I : Type)
    {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩) (i : I) :
    piZdiscLocallyConstantSectionsEquiv I T'
        ((∏ᶜ fun _ : I => IntProof.Zdisc).obj.map f.op x) i =
      (piZdiscLocallyConstantSectionsEquiv I T x i).comap f.hom.hom := by
  dsimp [piZdiscLocallyConstantSectionsEquiv]
  rw [LightCondMod.hom_naturality_apply ℤ
    (Limits.Pi.π (fun _ : I => IntProof.Zdisc) i) f.op x]
  exact ProjectiveGeneratorProof.zdiscSectionsEquiv_map f
    ((Limits.Pi.π (fun _ : I => IntProof.Zdisc) i).hom.app ⟨T⟩ x)

/-- The finite-support sequence description of maps from `P ℤ` is additive. -/
lemma nullSeqPointsEquiv_sub (T : LightProfinite)
    (f g : P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ IntProof.Zdisc) :
    IntProof.nullSeqPointsEquiv T (f - g) =
      IntProof.nullSeqPointsEquiv T f - IntProof.nullSeqPointsEquiv T g := by
  ext t n
  change IntProof.nullSeqPointsEquiv T (f - g) t n =
    IntProof.nullSeqPointsEquiv T f t n - IntProof.nullSeqPointsEquiv T g t n
  rw [IntProof.nullSeqPointsEquiv_apply, IntProof.nullSeqPointsEquiv_apply,
    IntProof.nullSeqPointsEquiv_apply]
  rw [IntProof.pTensorHomSubtypeEquiv_apply_coe,
    IntProof.pTensorHomSubtypeEquiv_apply_coe,
    IntProof.pTensorHomSubtypeEquiv_apply_coe]
  rw [Preadditive.comp_sub]
  exact IntProof.freeProductHomEquiv_sub_apply (ℕ∪{∞} : LightProfinite) T _ _ _

/-- Sections of the internal dual of `P ℤ` are locally constant families of finitely supported
integer sequences. -/
noncomputable def internalDualPSectionsEquiv (T : LightProfinite) :
    (internalDual (P ℤ)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      LocallyConstant T IntProof.SeqZ := by
  let e₁ := ihomPointsLinearEquiv (P ℤ) IntProof.Zdisc T
  let e₂ : (P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ IntProof.Zdisc) ≃+
      LocallyConstant T IntProof.SeqZ :=
    { IntProof.nullSeqPointsEquiv T with
      map_add' := by
        intro f g
        change IntProof.nullSeqPointsEquiv T (f + g) =
          IntProof.nullSeqPointsEquiv T f + IntProof.nullSeqPointsEquiv T g
        rw [← sub_eq_iff_eq_add]
        simpa only [add_sub_cancel_right] using (nullSeqPointsEquiv_sub T (f + g) g).symm }
  exact e₁.trans e₂.toIntLinearEquiv

lemma internalDualPSectionsEquiv_restrict {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual (P ℤ)).obj.obj ⟨T⟩) :
    internalDualPSectionsEquiv T' ((internalDual (P ℤ)).obj.map f.op x) =
      (internalDualPSectionsEquiv T x).comap f.hom.hom := by
  let q := ihomPoints ℤ (P ℤ) IntProof.Zdisc T x
  have hq : ihomPoints ℤ (P ℤ) IntProof.Zdisc T'
        ((internalDual (P ℤ)).obj.map f.op x) =
      (P ℤ ◁ (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ q := by
    apply (ihomPoints ℤ (P ℤ) IntProof.Zdisc T').symm.injective
    rw [Equiv.symm_apply_apply]
    rw [ihomPoints_symm_comp]
    simp [q]
  ext t n
  change IntProof.nullSeqPointsEquiv T'
      (ihomPoints ℤ (P ℤ) IntProof.Zdisc T'
        ((internalDual (P ℤ)).obj.map f.op x)) t n =
    IntProof.nullSeqPointsEquiv T q (f t) n
  rw [hq]
  rw [IntProof.nullSeqPointsEquiv_apply, IntProof.nullSeqPointsEquiv_apply]
  rw [IntProof.pTensorHomSubtypeEquiv_apply_coe,
    IntProof.pTensorHomSubtypeEquiv_apply_coe]
  rw [← Category.assoc]
  rw [← MonoidalCategory.whisker_exchange]
  rw [Category.assoc]
  change IntProof.freeProductHomEquiv (ℕ∪{∞} : LightProfinite) T'
      (((free ℤ).obj (ℕ∪{∞}).toCondensed ◁
        (free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫
          ((P_proj ℤ ▷ (free ℤ).obj T.toCondensed) ≫ q)) ((n : ℕ∪{∞}), t) = _
  rw [freeProductHomEquiv_precomp_right]
  rfl

/-- The sectionwise comparison between the internal dual of `P ℤ` and the discrete finite-support
sequence module. -/
noncomputable def internalDualPDiscreteSectionsEquiv (T : LightProfinite) :
    (internalDual (P ℤ)).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ IntProof.SeqZ)).obj.obj ⟨T⟩ :=
  (internalDualPSectionsEquiv T).trans
    (discreteModuleSectionsLinearEquiv T (ModuleCat.of ℤ IntProof.SeqZ)).symm

lemma internalDualPDiscreteSectionsEquiv_restrict {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual (P ℤ)).obj.obj ⟨T⟩) :
    internalDualPDiscreteSectionsEquiv T'
        ((internalDual (P ℤ)).obj.map f.op x) =
      ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ IntProof.SeqZ)).obj.map f.op
          (internalDualPDiscreteSectionsEquiv T x) := by
  apply (discreteModuleSectionsLinearEquiv T'
    (ModuleCat.of ℤ IntProof.SeqZ)).injective
  dsimp [internalDualPDiscreteSectionsEquiv]
  rw [LinearEquiv.apply_symm_apply]
  dsimp [discreteModuleSectionsLinearEquiv]
  rw [discreteModuleSectionsEquiv_restrict]
  rw [Equiv.apply_symm_apply]
  exact internalDualPSectionsEquiv_restrict f x

set_option maxRecDepth 10000 in
/-- The internal dual of `P ℤ` is the discrete module of finitely supported integer sequences. -/
noncomputable def internalDualPIso :
    internalDual (P ℤ) ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ IntProof.SeqZ) where
  hom := {
    hom := {
      app T := ModuleCat.ofHom (internalDualPDiscreteSectionsEquiv T.unop).toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        exact internalDualPDiscreteSectionsEquiv_restrict f.unop x } }
  inv := {
    hom := {
      app T := ModuleCat.ofHom (internalDualPDiscreteSectionsEquiv T.unop).symm.toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        apply (internalDualPDiscreteSectionsEquiv T'.unop).injective
        change internalDualPDiscreteSectionsEquiv T'.unop
            ((internalDualPDiscreteSectionsEquiv T'.unop).symm
              (((LightCondensed.discrete (ModuleCat ℤ)).obj
                (ModuleCat.of ℤ IntProof.SeqZ)).obj.map f.unop.op x)) = _
        rw [LinearEquiv.apply_symm_apply]
        change ((LightCondensed.discrete (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ IntProof.SeqZ)).obj.map f.unop.op x =
          internalDualPDiscreteSectionsEquiv T'.unop
            ((internalDual (P ℤ)).obj.map f.unop.op
              ((internalDualPDiscreteSectionsEquiv T.unop).symm x))
        rw [internalDualPDiscreteSectionsEquiv_restrict]
        rw [LinearEquiv.apply_symm_apply] } }
  hom_inv_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualPDiscreteSectionsEquiv T.unop).symm_apply_apply x
  inv_hom_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualPDiscreteSectionsEquiv T.unop).apply_symm_apply x

/-- The internal dual of a discrete free module on `I` has the sections of an `I`-fold product
of discrete integers. -/
noncomputable def internalDualFinsuppProductSectionsEquiv (I : Type)
    (T : LightProfinite) :
    (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (I →₀ ℤ)))).obj.obj ⟨T⟩ ≃ₗ[ℤ]
      (∏ᶜ fun _ : I => IntProof.Zdisc).obj.obj ⟨T⟩ :=
  (internalDualDiscreteSectionsEquiv (ModuleCat.of ℤ (I →₀ ℤ)) T).trans
    (((Finsupp.basisSingleOne : Module.Basis I ℤ (I →₀ ℤ)).constr ℤ).symm.trans
      (piZdiscLocallyConstantSectionsEquiv I T).symm)

lemma internalDualFinsuppProductSectionsEquiv_restrict (I : Type)
    {T T' : LightProfinite} (f : T' ⟶ T)
    (x : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (I →₀ ℤ)))).obj.obj ⟨T⟩) :
    internalDualFinsuppProductSectionsEquiv I T'
        ((internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ (I →₀ ℤ)))).obj.map f.op x) =
      (∏ᶜ fun _ : I => IntProof.Zdisc).obj.map f.op
        (internalDualFinsuppProductSectionsEquiv I T x) := by
  apply (piZdiscLocallyConstantSectionsEquiv I T').injective
  ext i
  rw [piZdiscLocallyConstantSectionsEquiv_restrict]
  dsimp [internalDualFinsuppProductSectionsEquiv]
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [internalDualDiscreteSectionsEquiv_restrict]
  rfl

set_option maxRecDepth 10000 in
/-- The internal dual of the discrete direct sum `⊕ I, ℤ` is the product `∏ I, ℤ`. -/
noncomputable def internalDualFinsuppIsoProduct (I : Type) :
    internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (I →₀ ℤ))) ≅
      ∏ᶜ fun _ : I => IntProof.Zdisc where
  hom := {
    hom := {
      app T := ModuleCat.ofHom (internalDualFinsuppProductSectionsEquiv I T.unop).toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        exact internalDualFinsuppProductSectionsEquiv_restrict I f.unop x } }
  inv := {
    hom := {
      app T := ModuleCat.ofHom
        (internalDualFinsuppProductSectionsEquiv I T.unop).symm.toLinearMap
      naturality := by
        intro T T' f
        rw [show f = f.unop.op by rfl]
        ext x
        apply (internalDualFinsuppProductSectionsEquiv I T'.unop).injective
        change internalDualFinsuppProductSectionsEquiv I T'.unop
            ((internalDualFinsuppProductSectionsEquiv I T'.unop).symm
              ((∏ᶜ fun _ : I => IntProof.Zdisc).obj.map f.unop.op x)) = _
        rw [LinearEquiv.apply_symm_apply]
        change (∏ᶜ fun _ : I => IntProof.Zdisc).obj.map f.unop.op x =
          internalDualFinsuppProductSectionsEquiv I T'.unop
            ((internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ (I →₀ ℤ)))).obj.map f.unop.op
                ((internalDualFinsuppProductSectionsEquiv I T.unop).symm x))
        rw [internalDualFinsuppProductSectionsEquiv_restrict]
        rw [LinearEquiv.apply_symm_apply] } }
  hom_inv_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualFinsuppProductSectionsEquiv I T.unop).symm_apply_apply x
  inv_hom_id := by
    apply LightCondensed.hom_ext
    intro T
    ext x
    exact (internalDualFinsuppProductSectionsEquiv I T.unop).apply_symm_apply x

lemma internalDualFinsuppIsoProduct_hom_apply_coord (I : Type) (T : LightProfinite)
    (x : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ (I →₀ ℤ)))).obj.obj ⟨T⟩) (i : I) :
    ProjectiveGeneratorProof.zdiscSectionsEquiv T
        (((internalDualFinsuppIsoProduct I).hom ≫
          Limits.Pi.π (fun _ : I => IntProof.Zdisc) i).hom.app ⟨T⟩ x) =
      internalDualDiscreteSectionsEquiv (ModuleCat.of ℤ (I →₀ ℤ)) T x
        (Finsupp.single i 1) := by
  dsimp [internalDualFinsuppIsoProduct, internalDualFinsuppProductSectionsEquiv]
  change piZdiscLocallyConstantSectionsEquiv I T
      ((piZdiscLocallyConstantSectionsEquiv I T).symm
        (((Finsupp.basisSingleOne : Module.Basis I ℤ (I →₀ ℤ)).constr ℤ).symm
          (internalDualDiscreteSectionsEquiv (ModuleCat.of ℤ (I →₀ ℤ)) T x))) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The double internal dual of `P ℤ` is the countable product of discrete integers. -/
noncomputable def doubleInternalDualPIsoProduct :
    doubleInternalDual (P ℤ) ≅ ∏ᶜ fun _ : ℕ => IntProof.Zdisc := by
  exact (MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).mapIso
      internalDualPIso.symm.op ≪≫
    internalDualFinsuppIsoProduct ℕ

/-- Evaluation of a double dual at a morphism to the coefficient object. -/
def doubleDualCoordinate {X : LightCondAb} (f : X ⟶ IntProof.Zdisc) :
    doubleInternalDual X ⟶ IntProof.Zdisc :=
  (λ_ (doubleInternalDual X)).inv ≫
    (MonoidalClosed.curry' f ▷ doubleInternalDual X) ≫
    (ihom.ev (internalDual X)).app IntProof.Zdisc

/-- Turn a section over the point into the corresponding global element. -/
noncomputable def pointSectionToGlobal (A : LightCondAb)
    (x : A.obj.obj ⟨LightProfinite.of PUnit.{1}⟩) : 𝟙_ LightCondAb ⟶ A :=
  ProjectiveGeneratorProof.freePointIsoUnit.inv ≫
    (ProjectiveGeneratorProof.freeHomEquivPoints
      (LightProfinite.of PUnit.{1}) A).symm x

/-- The global element of a discrete module determined by `m`. -/
noncomputable def discreteGlobalElement (M : ModuleCat ℤ) (m : M) :
    𝟙_ LightCondAb ⟶ (LightCondensed.discrete (ModuleCat ℤ)).obj M :=
  pointSectionToGlobal _
    ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
      ((LightCondensed.discrete (ModuleCat ℤ)).obj M))
        (𝟙 ((LightCondensed.discrete (ModuleCat ℤ)).obj M))).hom m)

lemma pointSectionToGlobal_naturality {A B : LightCondAb} (f : A ⟶ B)
    (x : A.obj.obj ⟨LightProfinite.of PUnit.{1}⟩) :
    pointSectionToGlobal A x ≫ f =
      pointSectionToGlobal B (f.hom.app ⟨LightProfinite.of PUnit.{1}⟩ x) := by
  dsimp [pointSectionToGlobal]
  rw [Category.assoc]
  congr 1
  apply (ProjectiveGeneratorProof.freeHomEquivPoints
    (LightProfinite.of PUnit.{1}) B).injective
  rw [ProjectiveGeneratorProof.freeHomEquivPoints_comp]
  rw [Equiv.apply_symm_apply]
  rw [Equiv.apply_symm_apply]

lemma discreteGlobalElement_naturality (M : ModuleCat ℤ) (m : M)
    {A : LightCondAb} (f : (LightCondensed.discrete (ModuleCat ℤ)).obj M ⟶ A) :
    discreteGlobalElement M m ≫ f =
      pointSectionToGlobal A
        ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M A) f).hom m) := by
  change pointSectionToGlobal _
      ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
        ((LightCondensed.discrete (ModuleCat ℤ)).obj M)) (𝟙 _)).hom m) ≫ f = _
  rw [pointSectionToGlobal_naturality]
  congr 2

set_option backward.isDefEq.respectTransparency false in
lemma discreteModuleSectionsEquiv_adjunction_identity (M : ModuleCat ℤ) (m : M) :
    ProjectiveGeneratorProof.discreteModuleSectionsEquiv
        (LightProfinite.of PUnit.{1}) M
      (show ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj
          ⟨LightProfinite.of PUnit.{1}⟩ from
        ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
          ((LightCondensed.discrete (ModuleCat ℤ)).obj M)) (𝟙 _)).hom m)) =
    LocallyConstant.const PUnit.{1} m := by
  rw [Adjunction.homEquiv_id]
  dsimp [ProjectiveGeneratorProof.discreteModuleSectionsEquiv]
  change (((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app M ≫
    (LightCondensed.underlying (ModuleCat ℤ)).map
      ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M)).hom m) = _
  let Y := (LightCondMod.LocallyConstant.functor ℤ).obj M
  let N := (LightCondensed.underlying (ModuleCat ℤ)).obj Y
  let a : M ⟶ N := (LightCondMod.LocallyConstant.functorIsoDiscreteAux₁ ℤ M).hom
  have hmor : (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app M ≫
        (LightCondensed.underlying (ModuleCat ℤ)).map
          ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M) = a := by
    dsimp [a, LightCondMod.LocallyConstant.functorIsoDiscrete,
      LightCondMod.LocallyConstant.functorIsoDiscreteComponents,
      LightCondMod.LocallyConstant.functorIsoDiscreteAux₂, NatIso.ofComponents]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, asIso_hom,
      Functor.map_comp]
    have hn : (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app M ≫
          (LightCondensed.underlying (ModuleCat ℤ)).map
            ((LightCondensed.discrete (ModuleCat ℤ)).map a) =
        a ≫ (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app
          N := by
      simpa [N, Y] using
        ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.naturality a).symm
    let b := (LightCondensed.underlying (ModuleCat ℤ)).map
      ((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).counit.app Y)
    have htri : (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app N ≫ b =
        𝟙 N := by
      simpa [N, Y, b] using
        (LightCondensed.discreteUnderlyingAdj
          (ModuleCat ℤ)).right_triangle_components Y
    calc
      _ = (a ≫ (LightCondensed.discreteUnderlyingAdj
          (ModuleCat ℤ)).unit.app N) ≫ b := by
            exact congrArg (fun k => k ≫ b) hn
      _ = a ≫ ((LightCondensed.discreteUnderlyingAdj
          (ModuleCat ℤ)).unit.app N ≫ b) := by simp only [Category.assoc]
      _ = a := by rw [htri]; simp
  rw [hmor]
  rfl

/-- The inverse right-unitor map, with the chosen one-point model of the tensor unit exposed. -/
noncomputable def rightPointUnit (S : LightProfinite) :
    S ⟶ S ⊗ LightProfinite.of PUnit.{1} :=
  (ρ_ S).inv

@[simp]
lemma rightPointUnit_apply (S : LightProfinite) (s : S) :
    rightPointUnit S s = (s, PUnit.unit) := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_rightUnit (S : LightProfinite) :
    (ρ_ ((free ℤ).obj S.toCondensed)).inv ≫
      ((free ℤ).obj S.toCondensed ◁ ProjectiveGeneratorProof.freePointIsoUnit.inv) ≫
      (IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S)) := by
  dsimp [IntProof.freeTensorIsoInt, ProjectiveGeneratorProof.freePointIsoUnit]
  simp [← Functor.map_comp]
  change (free ℤ).map
      ((ρ_ (lightProfiniteToLightCondSet.obj S)).inv ≫
        (lightProfiniteToLightCondSet.obj S ◁
          Functor.LaxMonoidal.ε lightProfiniteToLightCondSet) ≫
        Functor.LaxMonoidal.μ lightProfiniteToLightCondSet S (𝟙_ LightProfinite)) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S))
  change _ = (free ℤ).map (lightProfiniteToLightCondSet.map (ρ_ S).inv)
  rw [Functor.LaxMonoidal.right_unitality_inv]

@[reassoc]
lemma uncurry'_pointSectionToGlobal {X Y : LightCondAb}
    (h : (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (ihom X).obj Y) :
    MonoidalClosed.uncurry'
        (ProjectiveGeneratorProof.freePointIsoUnit.inv ≫ h) =
      (ρ_ X).inv ≫ (X ◁ ProjectiveGeneratorProof.freePointIsoUnit.inv) ≫
        MonoidalClosed.uncurry h := by
  dsimp only [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left]

lemma freeProductHomEquiv_eq_freeHomDiscrete (S T : LightProfinite)
    (f : (free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed ⟶ IntProof.Zdisc) :
    IntProof.freeProductHomEquiv S T f =
      IntProof.freeHomDiscreteEquiv ℤ (S ⊗ T : LightProfinite) (ModuleCat.of ℤ ℤ)
        ((IntProof.freeTensorIsoInt S T).inv ≫ f) := rfl

lemma zdisc_freeHomEquivPoints_eq_freeHomDiscrete (S : LightProfinite)
    (f : (free ℤ).obj S.toCondensed ⟶ IntProof.Zdisc) :
    ProjectiveGeneratorProof.zdiscSectionsEquiv S
        (ProjectiveGeneratorProof.freeHomEquivPoints S IntProof.Zdisc f) =
      IntProof.freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ) f := rfl

lemma freeProductHomEquiv_point_apply (S : LightProfinite)
    (g : (free ℤ).obj S.toCondensed ⊗
      (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ IntProof.Zdisc)
    (s : S) :
    IntProof.freeProductHomEquiv S (LightProfinite.of PUnit.{1}) g (s, PUnit.unit) =
      ProjectiveGeneratorProof.zdiscSectionsEquiv S
        (ProjectiveGeneratorProof.freeHomEquivPoints S IntProof.Zdisc
          ((ρ_ ((free ℤ).obj S.toCondensed)).inv ≫
            ((free ℤ).obj S.toCondensed ◁
              ProjectiveGeneratorProof.freePointIsoUnit.inv) ≫ g)) s := by
  rw [freeProductHomEquiv_eq_freeHomDiscrete]
  rw [zdisc_freeHomEquivPoints_eq_freeHomDiscrete]
  let f := (IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv ≫ g
  have hpre : (ρ_ ((free ℤ).obj S.toCondensed)).inv ≫
        ((free ℤ).obj S.toCondensed ◁
          ProjectiveGeneratorProof.freePointIsoUnit.inv) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S)) ≫
        (IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv :=
    ((IntProof.freeTensorIsoInt S
      (LightProfinite.of PUnit.{1})).eq_comp_inv).2
        (freeTensorIsoInt_hom_rightUnit S)
  have hpre_g : (ρ_ ((free ℤ).obj S.toCondensed)).inv ≫
        ((free ℤ).obj S.toCondensed ◁
          ProjectiveGeneratorProof.freePointIsoUnit.inv) ≫ g =
      (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S)) ≫ f := by
    simpa only [f, Category.assoc] using congrArg (fun k => k ≫ g) hpre
  rw [hpre_g]
  have hmap := IntProof.freeHomDiscreteEquiv_map (R := ℤ)
    (M := ModuleCat.of ℤ ℤ) (rightPointUnit S) f
  have hs := congrArg (fun q : LocallyConstant S ℤ => q s) hmap.symm
  change (IntProof.freeHomDiscreteEquiv ℤ
      (S ⊗ LightProfinite.of PUnit.{1} : LightProfinite) (ModuleCat.of ℤ ℤ) f)
        (rightPointUnit S s) = _ at hs
  simpa only [f, Category.assoc, rightPointUnit_apply] using hs

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
lemma internalDualFreeSectionsEquiv_point (S : LightProfinite)
    (x : (internalDual ((free ℤ).obj S.toCondensed)).obj.obj
      ⟨LightProfinite.of PUnit.{1}⟩) :
    internalDualFreeSectionsEquiv S (LightProfinite.of PUnit.{1}) x PUnit.unit =
      ProjectiveGeneratorProof.zdiscSectionsEquiv S
        (ProjectiveGeneratorProof.freeHomEquivPoints S IntProof.Zdisc
          (MonoidalClosed.uncurry' (pointSectionToGlobal _ x))) := by
  let h := (ProjectiveGeneratorProof.freeHomEquivPoints
    (LightProfinite.of PUnit.{1}) (internalDual ((free ℤ).obj S.toCondensed))).symm x
  have hmor : MonoidalClosed.uncurry'
      (ProjectiveGeneratorProof.freePointIsoUnit.inv ≫ h) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S)) ≫
        (IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv ≫
          MonoidalClosed.uncurry h := by
    rw [uncurry'_pointSectionToGlobal]
    have hpre : (ρ_ ((free ℤ).obj S.toCondensed)).inv ≫
          ((free ℤ).obj S.toCondensed ◁
            ProjectiveGeneratorProof.freePointIsoUnit.inv) =
        (free ℤ).map (lightProfiniteToLightCondSet.map (rightPointUnit S)) ≫
          (IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv := by
      exact ((IntProof.freeTensorIsoInt S
        (LightProfinite.of PUnit.{1})).eq_comp_inv).2
          (freeTensorIsoInt_hom_rightUnit S)
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ MonoidalClosed.uncurry h) hpre
  apply LocallyConstant.ext
  intro s
  change IntProof.freeProductHomEquiv S (LightProfinite.of PUnit.{1})
      (MonoidalClosed.uncurry h) (s, PUnit.unit) =
    ProjectiveGeneratorProof.zdiscSectionsEquiv S
      (ProjectiveGeneratorProof.freeHomEquivPoints S IntProof.Zdisc
        (MonoidalClosed.uncurry'
          (ProjectiveGeneratorProof.freePointIsoUnit.inv ≫ h))) s
  rw [hmor]
  rw [zdisc_freeHomEquivPoints_eq_freeHomDiscrete]
  rw [freeProductHomEquiv_eq_freeHomDiscrete]
  have hmap := IntProof.freeHomDiscreteEquiv_map (R := ℤ)
    (M := ModuleCat.of ℤ ℤ) (rightPointUnit S)
    ((IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv ≫
      MonoidalClosed.uncurry h)
  have hs := congrArg (fun q : LocallyConstant S ℤ => q s) hmap.symm
  change (IntProof.freeHomDiscreteEquiv ℤ
      (S ⊗ LightProfinite.of PUnit.{1} : LightProfinite) (ModuleCat.of ℤ ℤ)
        ((IntProof.freeTensorIsoInt S (LightProfinite.of PUnit.{1})).inv ≫
          MonoidalClosed.uncurry h)) (rightPointUnit S s) = _ at hs
  simpa using hs

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma uncurry'_global_curry_braiding {D F Z : LightCondAb}
    (d : 𝟙_ LightCondAb ⟶ D) (h : F ⟶ (ihom D).obj Z) :
    MonoidalClosed.uncurry'
        (d ≫ MonoidalClosed.curry ((β_ D F).inv ≫ MonoidalClosed.uncurry h)) =
      h ≫ (λ_ ((ihom D).obj Z)).inv ≫ (d ▷ (ihom D).obj Z) ≫
        (ihom.ev D).app Z := by
  dsimp only [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_eq]
  rw [BraidedCategory.braiding_inv_naturality_right_assoc]
  have hunit : (ρ_ F).inv ≫ (β_ (𝟙_ LightCondAb) F).inv = (λ_ F).inv := by
    exact ((β_ (𝟙_ LightCondAb) F).comp_inv_eq).2
      (leftUnitor_inv_braiding F).symm
  slice_lhs 1 2 => rw [hunit]
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
  rw [MonoidalCategory.whisker_exchange_assoc]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
lemma internalDualDiscreteSectionsEquiv_apply_basis (M : ModuleCat ℤ)
    (T : LightProfinite)
    (x : (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).obj.obj ⟨T⟩)
    (m : M) :
    internalDualDiscreteSectionsEquiv M T x m =
      ProjectiveGeneratorProof.zdiscSectionsEquiv T
        (((((λ_ (internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M))).inv ≫
          (discreteGlobalElement M m ▷
            internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj M)) ≫
          (ihom.ev ((LightCondensed.discrete (ModuleCat ℤ)).obj M)).app
            IntProof.Zdisc)).hom.app ⟨T⟩) x) := by
  let D := (LightCondensed.discrete (ModuleCat ℤ)).obj M
  let F := (free ℤ).obj T.toCondensed
  let h := (ProjectiveGeneratorProof.freeHomEquivPoints T (internalDual D)).symm x
  let q := MonoidalClosed.uncurry h
  let k : D ⟶ internalDual F :=
    MonoidalClosed.curry ((β_ D F).inv ≫ q)
  let y : (internalDual F).obj.obj ⟨LightProfinite.of PUnit.{1}⟩ :=
    ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
      (internalDual F)) k).hom m)
  change internalDualFreeSectionsEquiv T (LightProfinite.of PUnit.{1}) y PUnit.unit = _
  rw [internalDualFreeSectionsEquiv_point]
  have hy : discreteGlobalElement M m ≫ k = pointSectionToGlobal (internalDual F) y := by
    exact discreteGlobalElement_naturality M m k
  rw [← hy]
  rw [uncurry'_global_curry_braiding]
  let e : internalDual D ⟶ IntProof.Zdisc :=
    (λ_ (internalDual D)).inv ≫
      (discreteGlobalElement M m ▷ internalDual D) ≫
      (ihom.ev D).app IntProof.Zdisc
  change ProjectiveGeneratorProof.zdiscSectionsEquiv T
      (ProjectiveGeneratorProof.freeHomEquivPoints T IntProof.Zdisc (h ≫ e)) =
    ProjectiveGeneratorProof.zdiscSectionsEquiv T (e.hom.app ⟨T⟩ x)
  rw [ProjectiveGeneratorProof.freeHomEquivPoints_comp]
  have hh : ProjectiveGeneratorProof.freeHomEquivPoints T (internalDual D) h = x :=
    (ProjectiveGeneratorProof.freeHomEquivPoints T (internalDual D)).apply_symm_apply x
  rw [hh]

/-- The section over the chosen point associated to a global element. -/
noncomputable def globalToPoint (A : LightCondAb) (g : 𝟙_ LightCondAb ⟶ A) :
    A.obj.obj ⟨LightProfinite.of PUnit.{1}⟩ :=
  ProjectiveGeneratorProof.freeHomEquivPoints (LightProfinite.of PUnit.{1}) A
    (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ g)

@[simp]
lemma globalToPoint_pointSectionToGlobal (A : LightCondAb)
    (x : A.obj.obj ⟨LightProfinite.of PUnit.{1}⟩) :
    globalToPoint A (pointSectionToGlobal A x) = x := by
  dsimp [globalToPoint, pointSectionToGlobal]
  rw [Iso.hom_inv_id_assoc]
  rw [Equiv.apply_symm_apply]

@[simp]
lemma pointSectionToGlobal_globalToPoint (A : LightCondAb) (g : 𝟙_ LightCondAb ⟶ A) :
    pointSectionToGlobal A (globalToPoint A g) = g := by
  dsimp [globalToPoint, pointSectionToGlobal]
  rw [Equiv.symm_apply_apply]
  simp

lemma globalToPoint_naturality {A B : LightCondAb} (g : 𝟙_ LightCondAb ⟶ A)
    (f : A ⟶ B) :
    globalToPoint B (g ≫ f) = f.hom.app ⟨LightProfinite.of PUnit.{1}⟩
      (globalToPoint A g) := by
  dsimp [globalToPoint]
  rw [← Category.assoc]
  exact ProjectiveGeneratorProof.freeHomEquivPoints_comp _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Under the description of the internal dual of a free object as a discrete locally constant
function module, a global element is the functional represented by that locally constant
function. -/
lemma discreteGlobalElement_comp_internalDualFreeIso_inv (S : LightProfinite)
    (h : LocallyConstant S ℤ) :
    discreteGlobalElement (ModuleCat.of ℤ (LocallyConstant S ℤ)) h ≫
        (internalDualFreeIso S).inv =
      MonoidalClosed.curry' (ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h) := by
  apply (cancel_epi ProjectiveGeneratorProof.freePointIsoUnit.hom).1
  apply (ProjectiveGeneratorProof.freeHomEquivPoints
    (LightProfinite.of PUnit.{1}) (internalDual ((free ℤ).obj S.toCondensed))).injective
  change globalToPoint _
      (discreteGlobalElement (ModuleCat.of ℤ (LocallyConstant S ℤ)) h ≫
        (internalDualFreeIso S).inv) =
    globalToPoint _
      (MonoidalClosed.curry' (ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h))
  rw [globalToPoint_naturality]
  apply (internalDualFreeSectionsEquiv S (LightProfinite.of PUnit.{1})).injective
  let M := ModuleCat.of ℤ (LocallyConstant S ℤ)
  let x : ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj
      ⟨LightProfinite.of PUnit.{1}⟩ :=
    ((((LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).homEquiv M
      ((LightCondensed.discrete (ModuleCat ℤ)).obj M)) (𝟙 _)).hom h)
  have hx : globalToPoint ((LightCondensed.discrete (ModuleCat ℤ)).obj M)
      (discreteGlobalElement M h) = x := by
    change globalToPoint _ (pointSectionToGlobal _ x) = x
    rw [globalToPoint_pointSectionToGlobal]
  rw [hx]
  change internalDualFreeSectionsEquiv S (LightProfinite.of PUnit.{1})
      ((internalDualFreeDiscreteSectionsEquiv S
        (LightProfinite.of PUnit.{1})).symm x) = _
  rw [show internalDualFreeSectionsEquiv S (LightProfinite.of PUnit.{1})
      ((internalDualFreeDiscreteSectionsEquiv S
        (LightProfinite.of PUnit.{1})).symm x) =
      discreteModuleSectionsLinearEquiv (LightProfinite.of PUnit.{1}) M x by
    simp [internalDualFreeDiscreteSectionsEquiv, M]]
  have hx' : discreteModuleSectionsLinearEquiv (LightProfinite.of PUnit.{1}) M x =
      LocallyConstant.const PUnit.{1} h := by
    exact discreteModuleSectionsEquiv_adjunction_identity M h
  rw [hx']
  apply LocallyConstant.ext
  intro u
  cases u
  rw [internalDualFreeSectionsEquiv_point]
  rw [pointSectionToGlobal_globalToPoint]
  rw [MonoidalClosed.uncurry'_curry']
  rw [ProjectiveGeneratorProof.freeHomEquivPoints_zdiscMapOfLocallyConstant]
  exact (ProjectiveGeneratorProof.zdiscSectionsEquiv S).apply_symm_apply h |>.symm

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
lemma internalDualPIso_curry_basis (i : ℕ) :
    MonoidalClosed.curry'
        (ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i) ≫
      internalDualPIso.hom =
    discreteGlobalElement (ModuleCat.of ℤ IntProof.SeqZ) (Finsupp.single i 1) := by
  apply (cancel_epi ProjectiveGeneratorProof.freePointIsoUnit.hom).1
  apply (ProjectiveGeneratorProof.freeHomEquivPoints
    (LightProfinite.of PUnit.{1})
    ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ IntProof.SeqZ))).injective
  change globalToPoint _
      (MonoidalClosed.curry'
        (ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i) ≫
          internalDualPIso.hom) =
    globalToPoint _
      (discreteGlobalElement (ModuleCat.of ℤ IntProof.SeqZ) (Finsupp.single i 1))
  rw [globalToPoint_naturality]
  change _ = globalToPoint _ (pointSectionToGlobal _ _)
  rw [globalToPoint_pointSectionToGlobal]
  apply (ProjectiveGeneratorProof.discreteModuleSectionsEquiv
    (LightProfinite.of PUnit.{1}) (ModuleCat.of ℤ IntProof.SeqZ)).injective
  change ProjectiveGeneratorProof.discreteModuleSectionsEquiv
      (LightProfinite.of PUnit.{1}) (ModuleCat.of ℤ IntProof.SeqZ)
        (internalDualPDiscreteSectionsEquiv (LightProfinite.of PUnit.{1})
          (globalToPoint (internalDual (P ℤ))
            (MonoidalClosed.curry'
              (ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i)))) = _
  dsimp only [internalDualPDiscreteSectionsEquiv]
  change (discreteModuleSectionsLinearEquiv (LightProfinite.of PUnit.{1})
      (ModuleCat.of ℤ IntProof.SeqZ))
        ((discreteModuleSectionsLinearEquiv (LightProfinite.of PUnit.{1})
          (ModuleCat.of ℤ IntProof.SeqZ)).symm
            (internalDualPSectionsEquiv (LightProfinite.of PUnit.{1})
              (globalToPoint (internalDual (P ℤ))
                (MonoidalClosed.curry'
                  (ProjectiveGeneratorProof.basisMap ≫
                    ProjectiveGeneratorProof.boundedCoord i))))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [discreteModuleSectionsEquiv_adjunction_identity]
  ext u n
  cases u
  let ψ := ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i
  dsimp [internalDualPSectionsEquiv]
  change IntProof.nullSeqPointsEquiv (LightProfinite.of PUnit.{1})
      (ihomPoints ℤ (P ℤ) IntProof.Zdisc (LightProfinite.of PUnit.{1})
        (globalToPoint (internalDual (P ℤ)) (MonoidalClosed.curry' ψ)))
        PUnit.unit n = (Finsupp.single i 1) n
  have hrep : (ProjectiveGeneratorProof.freeHomEquivPoints
        (LightProfinite.of PUnit.{1}) (internalDual (P ℤ))).symm
      (globalToPoint (internalDual (P ℤ)) (MonoidalClosed.curry' ψ)) =
        ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ MonoidalClosed.curry' ψ := by
    dsimp [globalToPoint]
    rw [Equiv.symm_apply_apply]
  have hq : ihomPoints ℤ (P ℤ) IntProof.Zdisc (LightProfinite.of PUnit.{1})
        (globalToPoint (internalDual (P ℤ)) (MonoidalClosed.curry' ψ)) =
      MonoidalClosed.uncurry
        (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ MonoidalClosed.curry' ψ) := by
    rw [ihomPoints_apply]
    exact congrArg MonoidalClosed.uncurry hrep
  rw [hq]
  change IntProof.nullSeqPointsEquiv (LightProfinite.of PUnit.{1})
    (MonoidalClosed.uncurry
      (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ MonoidalClosed.curry' ψ))
      PUnit.unit n = (Finsupp.single i 1) n
  rw [IntProof.nullSeqPointsEquiv_apply]
  rw [IntProof.pTensorHomSubtypeEquiv_apply_coe]
  change IntProof.freeProductHomEquiv (ℕ∪{∞} : LightProfinite)
      (LightProfinite.of PUnit.{1})
        (((P_proj ℤ) ▷
            (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) ≫
          MonoidalClosed.uncurry
            (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫
              MonoidalClosed.curry' ψ))
        ((n : ℕ∪{∞}), PUnit.unit) = (Finsupp.single i 1) n
  rw [freeProductHomEquiv_point_apply]
  have hcurry : MonoidalClosed.uncurry
        (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ MonoidalClosed.curry' ψ) =
      ((P ℤ) ◁ ProjectiveGeneratorProof.freePointIsoUnit.hom) ≫
        (ρ_ (P ℤ)).hom ≫ ψ := by
    rw [MonoidalClosed.uncurry_natural_left]
    dsimp only [MonoidalClosed.curry']
    rw [MonoidalClosed.uncurry_curry]
  have hlong : (ρ_ ((free ℤ).obj (ℕ∪{∞}).toCondensed)).inv ≫
        ((free ℤ).obj (ℕ∪{∞}).toCondensed ◁
          ProjectiveGeneratorProof.freePointIsoUnit.inv) ≫
        ((P_proj ℤ) ▷ (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) ≫
        MonoidalClosed.uncurry
          (ProjectiveGeneratorProof.freePointIsoUnit.hom ≫ MonoidalClosed.curry' ψ) =
      P_proj ℤ ≫ ψ := by
    rw [hcurry]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.rightUnitor_inv_naturality_assoc]
    simp
  rw [hlong]
  dsimp only [ψ]
  rw [ProjectiveGeneratorProof.P_proj_comp_basisMap_boundedCoord]
  rw [ProjectiveGeneratorProof.zdiscSectionsEquiv_zdiscMapOfLocallyConstant]
  rw [ProjectiveGeneratorProof.boundedStandardBasisCoord_finite]
  by_cases hn : n = i
  · subst n
    simp
  · simp [hn]

lemma discreteGlobalElement_internalDualPIso_inv (i : ℕ) :
    discreteGlobalElement (ModuleCat.of ℤ IntProof.SeqZ) (Finsupp.single i 1) ≫
        internalDualPIso.inv =
      MonoidalClosed.curry'
        (ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i) := by
  rw [← internalDualPIso_curry_basis]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pre_comp_evaluationAtGlobal {A B : LightCondAb} (f : B ⟶ A)
    (d : 𝟙_ LightCondAb ⟶ B) :
    (MonoidalClosed.pre f).app IntProof.Zdisc ≫
        (λ_ (internalDual B)).inv ≫ (d ▷ internalDual B) ≫
          (ihom.ev B).app IntProof.Zdisc =
      (λ_ (internalDual A)).inv ≫ ((d ≫ f) ▷ internalDual A) ≫
        (ihom.ev A).app IntProof.Zdisc := by
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
  rw [MonoidalCategory.whisker_exchange_assoc]
  rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
  simp only [comp_whiskerRight, Category.assoc]

@[reassoc]
lemma doubleDualEvaluation_coordinate {X : LightCondAb} (f : X ⟶ IntProof.Zdisc) :
    doubleDualEvaluation X ≫ doubleDualCoordinate f = f := by
  dsimp only [doubleDualCoordinate, doubleDualEvaluation, doubleInternalDual, internalDual]
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
  rw [MonoidalCategory.whisker_exchange_assoc]
  slice_lhs 3 4 =>
    change MonoidalClosed.uncurry (MonoidalClosed.curry
      ((β_ ((ihom X).obj IntProof.Zdisc) X).hom ≫
        (ihom.ev X).app IntProof.Zdisc))
    rw [MonoidalClosed.uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [leftUnitor_inv_braiding_assoc]
  change MonoidalClosed.uncurry' (MonoidalClosed.curry' f) = f
  exact MonoidalClosed.uncurry'_curry' f

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise double-dual description evaluates a functional at the locally constant
function representing a morphism to the discrete integers. -/
lemma doubleDualFreeSectionsEquiv_apply (S T : LightProfinite)
    (x : (doubleDualCompletedFree S).obj.obj ⟨T⟩) (h : LocallyConstant S ℤ) :
    doubleDualFreeSectionsEquiv S T x h =
      ProjectiveGeneratorProof.zdiscSectionsEquiv T
        ((doubleDualCoordinate
          (ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h)).hom.app ⟨T⟩ x) := by
  let e := internalDualFreeIso S
  let M := ModuleCat.of ℤ (LocallyConstant S ℤ)
  let D := (LightCondensed.discrete (ModuleCat ℤ)).obj M
  let d := discreteGlobalElement M h
  let ψ := ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h
  let p := (MonoidalClosed.pre e.inv).app IntProof.Zdisc
  let evd : internalDual D ⟶ IntProof.Zdisc :=
    (λ_ (internalDual D)).inv ≫ (d ▷ internalDual D) ≫
      (ihom.ev D).app IntProof.Zdisc
  let y := p.hom.app ⟨T⟩ x
  change internalDualDiscreteSectionsEquiv M T y h = _
  rw [internalDualDiscreteSectionsEquiv_apply_basis]
  have hy : y = p.hom.app ⟨T⟩ x := rfl
  rw [hy]
  change ProjectiveGeneratorProof.zdiscSectionsEquiv T
      ((p ≫ evd).hom.app ⟨T⟩ x) =
    ProjectiveGeneratorProof.zdiscSectionsEquiv T
      ((doubleDualCoordinate ψ).hom.app ⟨T⟩ x)
  rw [show p ≫ evd =
      (λ_ (internalDual (internalDual ((free ℤ).obj S.toCondensed)))).inv ≫
        ((d ≫ e.inv) ▷
          internalDual (internalDual ((free ℤ).obj S.toCondensed))) ≫
          (ihom.ev (internalDual ((free ℤ).obj S.toCondensed))).app IntProof.Zdisc by
    exact pre_comp_evaluationAtGlobal e.inv d]
  rw [discreteGlobalElement_comp_internalDualFreeIso_inv S h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Under the sectionwise description, double-dual evaluation is the usual pairing with locally
constant integer-valued functions. -/
lemma doubleDualFreeSectionsEquiv_evaluation (S T : LightProfinite)
    (x : (lightProfiniteFreeℤ.obj S).obj.obj ⟨T⟩) (h : LocallyConstant S ℤ) :
    doubleDualFreeSectionsEquiv S T
        ((doubleDualCompletion.app S).hom.app ⟨T⟩ x) h =
      ProjectiveGeneratorProof.zdiscSectionsEquiv T
        ((ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h).hom.app ⟨T⟩ x) := by
  rw [doubleDualFreeSectionsEquiv_apply]
  change ProjectiveGeneratorProof.zdiscSectionsEquiv T
      (((doubleDualCompletion.app S ≫ doubleDualCoordinate
        (ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h)).hom.app ⟨T⟩) x) = _
  have he : doubleDualCompletion.app S ≫ doubleDualCoordinate
      (ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h) =
      ProjectiveGeneratorProof.zdiscMapOfLocallyConstant S h := by
    exact doubleDualEvaluation_coordinate _
  rw [he]
  rfl

/-- On a finite light profinite set, every integer-valued function is locally constant. -/
noncomputable def finiteLocallyConstantLinearEquiv (F : LightProfinite) [Finite F] :
    LocallyConstant F ℤ ≃ₗ[ℤ] (F → ℤ) where
  toFun f := f
  invFun f :=
    { toFun := f
      isLocallyConstant :=
        (IsLocallyConstant.iff_continuous f).mpr continuous_of_discreteTopology }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Locally constant maps into a finite product are the same as finite families of locally
constant maps. -/
noncomputable def locallyConstantPiLinearEquiv (F T : LightProfinite) [Finite F] :
    LocallyConstant T (F → ℤ) ≃ₗ[ℤ] (F → LocallyConstant T ℤ) where
  toFun x a := x.map (fun f => f a)
  invFun x :=
    { toFun := fun t a => x a t
      isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr
        (continuous_pi fun a =>
          (IsLocallyConstant.iff_continuous _).mp (x a).isLocallyConstant) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The standard finite-stage cocone presenting the locally constant integer-valued functions on
`S`. -/
noncomputable def locallyConstantIntSequentialCocone (S : LightProfinite) :
    Cocone (S.diagram.rightOp ⋙ locallyConstantIntModulePresheaf) :=
  locallyConstantIntModulePresheaf.mapCocone
    (coconeRightOpOfCone S.asLimitCone)

/-- Locally constant integer-valued functions on `S` are the filtered colimit of the functions on
its standard finite stages. -/
noncomputable def locallyConstantIntSequentialCoconeIsColimit (S : LightProfinite) :
    IsColimit (locallyConstantIntSequentialCocone S) := by
  apply isColimitOfReflects (CategoryTheory.forget (ModuleCat ℤ))
  exact LightCondensed.isColimitLocallyConstantPresheafDiagram ℤ S

set_option backward.isDefEq.respectTransparency false in
/-- Double-dual evaluation is an isomorphism on free objects generated by finite light
profinite sets. -/
lemma isIso_doubleDualCompletion_app_of_finite (F : LightProfinite) [Finite F] :
    IsIso (doubleDualCompletion.app F) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))]
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rcases T with ⟨T⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((doubleDualCompletion.app F).hom.app ⟨T⟩)
  constructor
  · intro x y hxy
    apply ProjectiveGeneratorProof.finiteFree_section_ext_of_zdisc_eval F T x y
    intro ψ
    let h : LocallyConstant F ℤ :=
      ProjectiveGeneratorProof.zdiscSectionsEquiv F
        (ProjectiveGeneratorProof.freeHomEquivPoints F IntProof.Zdisc ψ)
    have hψ : ProjectiveGeneratorProof.zdiscMapOfLocallyConstant F h = ψ :=
      ProjectiveGeneratorProof.zdiscMapOfLocallyConstant_of_freeHomEquivPoints F ψ
    apply (ProjectiveGeneratorProof.zdiscSectionsEquiv T).injective
    rw [← hψ]
    rw [← doubleDualFreeSectionsEquiv_evaluation F T x h]
    rw [← doubleDualFreeSectionsEquiv_evaluation F T y h]
    rw [hxy]
  · intro y
    letI := Fintype.ofFinite F
    letI := Classical.decEq F
    let L : LocallyConstant F ℤ →ₗ[ℤ] LocallyConstant T ℤ :=
      doubleDualFreeSectionsEquiv F T y
    let eF := finiteLocallyConstantLinearEquiv F
    let L' : (F → ℤ) →ₗ[ℤ] LocallyConstant T ℤ :=
      (LinearEquiv.congrLeft (LocallyConstant T ℤ) ℤ eF) L
    let coeff : F → LocallyConstant T ℤ :=
      LinearEquiv.piRing ℤ (LocallyConstant T ℤ) F ℤ L'
    let τ : TopologicalSpace (F →₀ ℤ) :=
      inferInstanceAs (TopologicalSpace ↑(LightCondAb.topologicalFree F).toModuleCat)
    letI : TopologicalSpace (F →₀ ℤ) := τ
    let μlc : LocallyConstant T (F →₀ ℤ) :=
      ((locallyConstantPiLinearEquiv F T).symm coeff).map
        (Finsupp.linearEquivFunOnFinite ℤ ℤ F).symm
    let μ : C(↑T.toTop, ↑(LightCondAb.topologicalFree F).toModuleCat) :=
      ⟨μlc, μlc.isLocallyConstant.continuous⟩
    let x : (lightProfiniteFreeℤ.obj F).obj.obj ⟨T⟩ :=
      (LightCondAb.freeTopologicalFreeIso F).inv.hom.app ⟨T⟩ μ
    refine ⟨x, ?_⟩
    apply (doubleDualFreeSectionsEquiv F T).injective
    apply LinearMap.ext
    intro h
    rw [doubleDualFreeSectionsEquiv_evaluation]
    rw [ProjectiveGeneratorProof.zdiscMapOfLocallyConstant_eq_freeToTopologicalFree_eval]
    change ProjectiveGeneratorProof.zdiscSectionsEquiv T
        ((LightCondAb.topologicalFreeEvalDiscrete F h).hom.app ⟨T⟩
          ((LightCondAb.freeToTopologicalFree F).hom.app ⟨T⟩ x)) = L h
    have hx : (LightCondAb.freeToTopologicalFree F).hom.app ⟨T⟩ x = μ := by
      exact LightCondAb.freeToTopologicalFree_app_section_of_iso_symm F T μ
    rw [hx]
    apply LocallyConstant.ext
    intro t
    rw [ProjectiveGeneratorProof.zdiscSectionsEquiv_topologicalFreeEvalDiscrete_apply]
    rw [LightCondAb.topologicalFreeEval_apply]
    have hL : L h = ∑ a : F, h a • coeff a := by
      calc
        L h = L' (eF h) := by rfl
        _ = (LinearEquiv.piRing ℤ (LocallyConstant T ℤ) F ℤ).symm coeff (eF h) := by
          rw [show coeff = LinearEquiv.piRing ℤ (LocallyConstant T ℤ) F ℤ L' by rfl]
          rw [LinearEquiv.symm_apply_apply]
        _ = ∑ a : F, h a • coeff a := by
          rw [LinearEquiv.piRing_symm_apply]
          rfl
    rw [hL]
    change (Finsupp.linearCombination ℤ fun s : F => h s)
        ((Finsupp.linearEquivFunOnFinite ℤ ℤ F).symm
          (((locallyConstantPiLinearEquiv F T).symm coeff) t)) =
      (∑ a : F, h a • coeff a) t
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype]
    · rw [show (∑ a : F, h a • coeff a) t =
          ∑ a : F, h a * coeff a t by
        have hsum := congrFun
          (map_sum (LocallyConstant.coeFnAddMonoidHom :
            LocallyConstant T ℤ →+ (T → ℤ))
              (fun a : F => h a • coeff a) Finset.univ) t
        calc
          _ = ∑ a : F, (h a • coeff a) t := by
            simpa only [LocallyConstant.coeFnAddMonoidHom_apply,
              Finset.sum_apply] using hsum
          _ = _ := by
            apply Finset.sum_congr rfl
            intro a ha
            rfl]
      apply Finset.sum_congr rfl
      intro a ha
      have hcoeff :
          ((Finsupp.linearEquivFunOnFinite ℤ ℤ F).symm
            (((locallyConstantPiLinearEquiv F T).symm coeff) t)) a = coeff a t := by
        change (Finsupp.linearEquivFunOnFinite ℤ ℤ F
          ((Finsupp.linearEquivFunOnFinite ℤ ℤ F).symm
            (((locallyConstantPiLinearEquiv F T).symm coeff) t))) a = coeff a t
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [hcoeff]
      rw [mul_comm]
      simp
    · intro a
      simp

/-- The discrete locally constant-function object is the filtered colimit of the corresponding
objects on the standard finite stages. -/
noncomputable def discreteLocallyConstantIntSequentialCocone (S : LightProfinite) :
    Cocone (S.diagram.rightOp ⋙ locallyConstantIntModulePresheaf ⋙
      LightCondensed.discrete (ModuleCat ℤ)) :=
  (LightCondensed.discrete (ModuleCat ℤ)).mapCocone
    (locallyConstantIntSequentialCocone S)

noncomputable def discreteLocallyConstantIntSequentialCoconeIsColimit
    (S : LightProfinite) :
    IsColimit (discreteLocallyConstantIntSequentialCocone S) := by
  letI : PreservesColimitsOfShape ℕ (LightCondensed.discrete (ModuleCat ℤ)) :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  exact isColimitOfPreserves (LightCondensed.discrete (ModuleCat ℤ))
    (locallyConstantIntSequentialCoconeIsColimit S)

/-- Dualizing the locally constant-function colimit gives its canonical inverse-limit cone. -/
noncomputable def internalDualDiscreteLocallyConstantSequentialCone (S : LightProfinite) :=
  (MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).mapCone
    (discreteLocallyConstantIntSequentialCocone S).op

/-- The cone obtained by dualizing the locally constant-function colimit is limiting. -/
noncomputable def internalDualDiscreteLocallyConstantSequentialConeIsLimit
    (S : LightProfinite) :
    IsLimit (internalDualDiscreteLocallyConstantSequentialCone S) :=
  isLimitOfPreserves (MonoidalClosed.internalHom.flip.obj IntProof.Zdisc)
    (discreteLocallyConstantIntSequentialCoconeIsColimit S).op

/-- Double-dual evaluation on a finite free object, bundled as an isomorphism. -/
noncomputable def finiteDoubleDualCompletionIso (F : FintypeCat) :
    finiteFreeℤ.obj F ≅
      (FintypeCat.toLightProfinite ⋙ doubleDualFree).obj F := by
  change finiteFreeℤ.obj F ≅
    doubleDualFree.obj (FintypeCat.toLightProfinite.obj F)
  letI : Finite F := F.property
  letI : Finite (FintypeCat.toLightProfinite.obj F) := by
    change Finite F
    infer_instance
  let e : finiteFreeℤ.obj F ⟶
      doubleDualFree.obj (FintypeCat.toLightProfinite.obj F) :=
    doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F)
  haveI : IsIso e := isIso_doubleDualCompletion_app_of_finite _
  exact asIso e

lemma finiteDoubleDualCompletionIso_hom (F : FintypeCat) :
    (finiteDoubleDualCompletionIso F).hom =
      doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) := by
  dsimp [finiteDoubleDualCompletionIso]

/-- Double-dual evaluation is a natural isomorphism on the finite free functor. -/
noncomputable def finiteDoubleDualCompletionNatIso :
    finiteFreeℤ ≅ FintypeCat.toLightProfinite ⋙ doubleDualFree :=
  NatIso.ofComponents finiteDoubleDualCompletionIso (by
    intro F G f
    rw [finiteDoubleDualCompletionIso_hom, finiteDoubleDualCompletionIso_hom]
    exact doubleDualCompletion.naturality (FintypeCat.toLightProfinite.map f))

@[simp]
lemma finiteDoubleDualCompletionNatIso_inv_app (F : FintypeCat) :
    finiteDoubleDualCompletionNatIso.inv.app F =
      (finiteDoubleDualCompletionIso F).inv := rfl

/-- On a finite set, evaluation and the locally constant-function description identify the free
object with the internal dual of its discrete function module. -/
noncomputable def finiteFreeIsoInternalDualDiscrete (F : FintypeCat) :
    finiteFreeℤ.obj F ≅
      internalDual ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ (LocallyConstant (FintypeCat.toLightProfinite.obj F) ℤ))) := by
  exact finiteDoubleDualCompletionIso F ≪≫
    doubleDualFreeIsoInternalDualDiscrete (FintypeCat.toLightProfinite.obj F)

lemma finiteFreeIsoInternalDualDiscrete_hom (F : FintypeCat) :
    (finiteFreeIsoInternalDualDiscrete F).hom =
      doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
        (doubleDualFreeNatIsoInternalDualDiscrete.hom.app
          (FintypeCat.toLightProfinite.obj F)) := by
  change (finiteDoubleDualCompletionIso F).hom ≫
      (doubleDualFreeIsoInternalDualDiscrete
        (FintypeCat.toLightProfinite.obj F)).hom = _
  rw [finiteDoubleDualCompletionIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The finite free functor is naturally the dual of the discrete locally constant-function
module. -/
noncomputable def finiteFreeNatIsoInternalDualDiscrete :
    finiteFreeℤ ≅
      FintypeCat.toLightProfinite ⋙ internalDualDiscreteLocallyConstantFunctor :=
  NatIso.ofComponents finiteFreeIsoInternalDualDiscrete (by
    intro F G f
    rw [finiteFreeIsoInternalDualDiscrete_hom,
      finiteFreeIsoInternalDualDiscrete_hom]
    change lightProfiniteFreeℤ.map (FintypeCat.toLightProfinite.map f) ≫
        (doubleDualCompletion.app (FintypeCat.toLightProfinite.obj G) ≫
          doubleDualFreeNatIsoInternalDualDiscrete.hom.app
            (FintypeCat.toLightProfinite.obj G)) =
      (doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
        doubleDualFreeNatIsoInternalDualDiscrete.hom.app
          (FintypeCat.toLightProfinite.obj F)) ≫
            internalDualDiscreteLocallyConstantFunctor.map
              (FintypeCat.toLightProfinite.map f)
    let q := FintypeCat.toLightProfinite.map f
    have h₁ := doubleDualCompletion.naturality q
    have h₂ := doubleDualFreeNatIsoInternalDualDiscrete.hom.naturality q
    calc
      lightProfiniteFreeℤ.map q ≫
          (doubleDualCompletion.app (FintypeCat.toLightProfinite.obj G) ≫
            doubleDualFreeNatIsoInternalDualDiscrete.hom.app
              (FintypeCat.toLightProfinite.obj G)) =
        (lightProfiniteFreeℤ.map q ≫
          doubleDualCompletion.app (FintypeCat.toLightProfinite.obj G)) ≫
            doubleDualFreeNatIsoInternalDualDiscrete.hom.app
              (FintypeCat.toLightProfinite.obj G) := Category.assoc _ _ _ |>.symm
      _ = (doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
          doubleDualFree.map q) ≫
            doubleDualFreeNatIsoInternalDualDiscrete.hom.app
              (FintypeCat.toLightProfinite.obj G) := by rw [h₁]
      _ = doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
          (doubleDualFree.map q ≫
            doubleDualFreeNatIsoInternalDualDiscrete.hom.app
              (FintypeCat.toLightProfinite.obj G)) := Category.assoc _ _ _
      _ = doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
          (doubleDualFreeNatIsoInternalDualDiscrete.hom.app
            (FintypeCat.toLightProfinite.obj F) ≫
              internalDualDiscreteLocallyConstantFunctor.map q) := by rw [h₂]
      _ = (doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
          doubleDualFreeNatIsoInternalDualDiscrete.hom.app
            (FintypeCat.toLightProfinite.obj F)) ≫
              internalDualDiscreteLocallyConstantFunctor.map q :=
        Category.assoc _ _ _ |>.symm)

@[simp]
lemma finiteFreeNatIsoInternalDualDiscrete_hom_app (F : FintypeCat) :
    finiteFreeNatIsoInternalDualDiscrete.hom.app F =
      (finiteFreeIsoInternalDualDiscrete F).hom := rfl

/-- The finite-stage diagram is naturally identified with the diagram obtained by dualizing the
locally constant-function colimit. -/
noncomputable def finiteFreeSequentialIsoInternalDualDiscrete (S : LightProfinite) :
    S.fintypeDiagram ⋙ finiteFreeℤ ≅
      (S.diagram.rightOp ⋙ locallyConstantIntModulePresheaf ⋙
        LightCondensed.discrete (ModuleCat ℤ)).op ⋙
          MonoidalClosed.internalHom.flip.obj IntProof.Zdisc :=
  NatIso.ofComponents (fun n => finiteFreeIsoInternalDualDiscrete
    (S.fintypeDiagram.obj n)) (by
      intro n m f
      exact finiteFreeNatIsoInternalDualDiscrete.hom.naturality
        (S.fintypeDiagram.map f))

/-- A limiting cone for the finite-stage free diagram, obtained by dualizing the locally
constant-function colimit and changing the finite-stage objects by evaluation. -/
noncomputable def doubleDualSequentialModelCone (S : LightProfinite) :
    Cone (S.fintypeDiagram ⋙ finiteFreeℤ) :=
  (Cone.postcompose (finiteFreeSequentialIsoInternalDualDiscrete S).inv).obj
    (internalDualDiscreteLocallyConstantSequentialCone S)

/-- The double dual of `ℤ[S]` is the limit of the free objects on the standard finite stages. -/
noncomputable def doubleDualSequentialModelConeIsLimit (S : LightProfinite) :
    IsLimit (doubleDualSequentialModelCone S) :=
  (IsLimit.postcomposeHomEquiv
    (finiteFreeSequentialIsoInternalDualDiscrete S).symm
      (internalDualDiscreteLocallyConstantSequentialCone S)).symm
        (internalDualDiscreteLocallyConstantSequentialConeIsLimit S)

/-- The inverse finite evaluation maps form the counit exhibiting the double-dual functor as a
right extension of the finite free functor. -/
noncomputable def doubleDualFreeCounit :
    FintypeCat.toLightProfinite ⋙ doubleDualFree ⟶ finiteFreeℤ :=
  finiteDoubleDualCompletionNatIso.inv

/-- The sequential cone associated to the double-dual right extension. -/
noncomputable def doubleDualFreeSequentialCone (S : LightProfinite) :
    Cone (S.fintypeDiagram ⋙ finiteFreeℤ) :=
  ((Functor.RightExtension.mk _ doubleDualFreeCounit).coneAt S).whisker
    (LightProfinite.Extend.functor S.asLimitCone)

/-- The model limit cone transported from the dualized locally constant-function colimit to have
point `doubleDualFree.obj S`. -/
noncomputable def doubleDualSequentialLimitCone (S : LightProfinite) :
    Cone (S.fintypeDiagram ⋙ finiteFreeℤ) :=
  (doubleDualSequentialModelCone S).extend
    (doubleDualFreeNatIsoInternalDualDiscrete.hom.app S)

/-- The transported double-dual cone is limiting. -/
noncomputable def doubleDualSequentialLimitConeIsLimit (S : LightProfinite) :
    IsLimit (doubleDualSequentialLimitCone S) :=
  IsLimit.ofIsoLimit (doubleDualSequentialModelConeIsLimit S)
    ((doubleDualSequentialModelCone S).extendIso
      (doubleDualFreeNatIsoInternalDualDiscrete.app S).symm)

noncomputable def doubleDualSequentialConePointIso (S : LightProfinite) :
    (doubleDualSequentialLimitCone S).pt ≅ (doubleDualFreeSequentialCone S).pt := by
  change doubleDualFree.obj S ≅ doubleDualFree.obj S
  exact Iso.refl _

@[simp]
lemma doubleDualSequentialConePointIso_hom (S : LightProfinite) :
    (doubleDualSequentialConePointIso S).hom = 𝟙 (doubleDualFree.obj S) := rfl

@[reassoc (attr := simp)]
lemma doubleDualSequentialConePointIso_hom_comp (S : LightProfinite) {X : LightCondAb}
    (f : (doubleDualFreeSequentialCone S).pt ⟶ X) :
    (doubleDualSequentialConePointIso S).hom ≫ f = f := by
  change (𝟙 (doubleDualFree.obj S)) ≫ f = f
  exact Category.id_comp f

set_option backward.isDefEq.respectTransparency false in
lemma doubleDualFreeSequentialCone_π (S : LightProfinite) (n : ℕ) :
    (doubleDualFreeSequentialCone S).π.app ⟨n⟩ =
      doubleDualFree.map (S.proj n) ≫
        (finiteDoubleDualCompletionIso (S.fintypeDiagram.obj ⟨n⟩)).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma doubleDualSequentialLimitCone_π (S : LightProfinite) (n : ℕ) :
    (doubleDualSequentialLimitCone S).π.app ⟨n⟩ =
      doubleDualFreeNatIsoInternalDualDiscrete.hom.app S ≫
        internalDualDiscreteLocallyConstantFunctor.map (S.proj n) ≫
          doubleDualFreeNatIsoInternalDualDiscrete.inv.app (S.component n) ≫
            (finiteDoubleDualCompletionIso (S.fintypeDiagram.obj ⟨n⟩)).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sequential right-extension cone agrees with the cone obtained by dualizing the locally
constant-function colimit. -/
noncomputable def doubleDualSequentialConeIso (S : LightProfinite) :
    doubleDualSequentialLimitCone S ≅ doubleDualFreeSequentialCone S :=
  Cone.ext (doubleDualSequentialConePointIso S) (by
    intro n
    rcases n with ⟨n⟩
    rw [doubleDualSequentialLimitCone_π, doubleDualFreeSequentialCone_π]
    have hcancel : doubleDualFreeNatIsoInternalDualDiscrete.hom.app S ≫
        internalDualDiscreteLocallyConstantFunctor.map (S.proj n) ≫
          doubleDualFreeNatIsoInternalDualDiscrete.inv.app (S.component n) =
      doubleDualFree.map (S.proj n) := by
      calc
        _ = (doubleDualFreeNatIsoInternalDualDiscrete.hom.app S ≫
            internalDualDiscreteLocallyConstantFunctor.map (S.proj n)) ≫
              doubleDualFreeNatIsoInternalDualDiscrete.inv.app (S.component n) :=
          Category.assoc _ _ _ |>.symm
        _ = (doubleDualFree.map (S.proj n) ≫
            doubleDualFreeNatIsoInternalDualDiscrete.hom.app (S.component n)) ≫
              doubleDualFreeNatIsoInternalDualDiscrete.inv.app (S.component n) := by
          rw [doubleDualFreeNatIsoInternalDualDiscrete.hom.naturality]
        _ = _ := by simp
    have hpoint : (doubleDualSequentialConePointIso S).hom ≫
        doubleDualFree.map (S.proj n) = doubleDualFree.map (S.proj n) := by
      exact doubleDualSequentialConePointIso_hom_comp S _
    let e := (finiteDoubleDualCompletionIso (S.fintypeDiagram.obj ⟨n⟩)).inv
    have h₁ := congrArg (fun k => k ≫ e) hcancel
    have h₂ := congrArg (fun k => k ≫ e) hpoint
    exact (by simpa only [Category.assoc] using h₁.trans h₂.symm))

/-- The double-dual right-extension cone over the standard finite presentation is limiting. -/
noncomputable def doubleDualFreeSequentialConeIsLimit (S : LightProfinite) :
    IsLimit (doubleDualFreeSequentialCone S) :=
  IsLimit.ofIsoLimit (doubleDualSequentialLimitConeIsLimit S)
    (doubleDualSequentialConeIso S)

/-- The double-dual functor with inverse finite-evaluation counit is a pointwise right Kan
extension of the finite free functor. -/
noncomputable def doubleDualFreeIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _ doubleDualFreeCounit).IsPointwiseRightKanExtension := by
  intro S
  letI : (LightProfinite.Extend.functor S.asLimitCone).Initial :=
    LightProfinite.Extend.functor_initial S.asLimitCone S.asLimit
  exact (Functor.Initial.isLimitWhiskerEquiv
    (LightProfinite.Extend.functor S.asLimitCone)
      ((Functor.RightExtension.mk _ doubleDualFreeCounit).coneAt S))
        (doubleDualFreeSequentialConeIsLimit S)

instance : doubleDualFree.IsRightKanExtension doubleDualFreeCounit :=
  doubleDualFreeIsPointwiseRightKanExtension.isRightKanExtension

/-- The right-Kan completed free functor is naturally isomorphic to the independently defined
double-internal-dual functor. -/
noncomputable def classicalCompletedFreeIsoDoubleDualFree :
    classicalCompletedFree ≅ doubleDualFree :=
  Functor.rightKanExtensionUnique classicalCompletedFree classicalCompletedFreeCounit
    doubleDualFree doubleDualFreeCounit

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from the right-Kan construction to the double dual identifies their canonical
maps from the ordinary free functor. -/
lemma classicalCompletion_comp_comparison :
    classicalCompletion ≫ classicalCompletedFreeIsoDoubleDualFree.hom =
      doubleDualCompletion := by
  apply doubleDualFree.hom_ext_of_isRightKanExtension doubleDualFreeCounit
  simp [classicalCompletedFreeIsoDoubleDualFree, classicalCompletion,
    doubleDualFreeCounit, finiteDoubleDualCompletionNatIso]
  symm
  apply NatTrans.ext
  funext F
  change doubleDualCompletion.app (FintypeCat.toLightProfinite.obj F) ≫
      (finiteDoubleDualCompletionIso F).inv = 𝟙 _
  rw [← finiteDoubleDualCompletionIso_hom]
  simp

/-- Pointwise form of compatibility between the right-Kan and double-dual completion maps. -/
@[reassoc]
lemma classicalCompletion_app_comp_comparison (S : LightProfinite) :
    classicalCompletion.app S ≫ classicalCompletedFreeIsoDoubleDualFree.hom.app S =
      doubleDualCompletion.app S := by
  exact NatTrans.congr_app classicalCompletion_comp_comparison S

/-- Precomposition with the comparison isomorphism identifies maps out of the double-dual and
right-Kan completed free objects. -/
noncomputable def comparisonPrecompEquiv (S : LightProfinite) (A : LightCondAb) :
    (doubleDualFree.obj S ⟶ A) ≃ (classicalCompletedFree.obj S ⟶ A) where
  toFun g := classicalCompletedFreeIsoDoubleDualFree.hom.app S ≫ g
  invFun g := classicalCompletedFreeIsoDoubleDualFree.inv.app S ≫ g
  left_inv g := by simp
  right_inv g := by simp

@[simp]
lemma comparisonPrecompEquiv_apply (S : LightProfinite) (A : LightCondAb)
    (g : doubleDualFree.obj S ⟶ A) :
    comparisonPrecompEquiv S A g =
      classicalCompletedFreeIsoDoubleDualFree.hom.app S ≫ g := rfl

/-- The right-Kan and double-dual formulations of the classical extension condition are
equivalent. -/
theorem classicalIsSolid_iff_doubleDualExtensionProperty (A : LightCondAb) :
    classicalIsSolid A ↔ doubleDualExtensionProperty A := by
  rw [classicalIsSolid, doubleDualExtensionProperty]
  constructor
  · intro h S
    let q := comparisonPrecompEquiv S A
    let p := fun g : classicalCompletedFree.obj S ⟶ A => classicalCompletion.app S ≫ g
    have hq := Function.Bijective.of_comp_iff p q.bijective
    have hpq : p ∘ q =
        (fun g : doubleDualCompletedFree S ⟶ A => doubleDualCompletionMap S ≫ g) := by
      funext g
      dsimp only [p, Function.comp_apply]
      rw [show q g = comparisonPrecompEquiv S A g from rfl,
        comparisonPrecompEquiv_apply]
      rw [← Category.assoc, classicalCompletion_app_comp_comparison]
      rfl
    have hp : Function.Bijective (p ∘ q) := hq.mpr (h S)
    rwa [hpq] at hp
  · intro h S
    let q := comparisonPrecompEquiv S A
    let p := fun g : classicalCompletedFree.obj S ⟶ A => classicalCompletion.app S ≫ g
    have hq := Function.Bijective.of_comp_iff p q.bijective
    apply hq.mp
    have hpq : p ∘ q =
        (fun g : doubleDualCompletedFree S ⟶ A => doubleDualCompletionMap S ≫ g) := by
      funext g
      dsimp only [p, Function.comp_apply]
      rw [show q g = comparisonPrecompEquiv S A g from rfl,
        comparisonPrecompEquiv_apply]
      rw [← Category.assoc, classicalCompletion_app_comp_comparison]
      rfl
    rw [hpq]
    exact h S


set_option maxRecDepth 10000 in
lemma doubleInternalDualPIsoProduct_hom_π (i : ℕ) :
    doubleInternalDualPIsoProduct.hom ≫
        Limits.Pi.π (fun _ : ℕ => IntProof.Zdisc) i =
      doubleDualCoordinate (ProjectiveGeneratorProof.basisMap ≫
        ProjectiveGeneratorProof.boundedCoord i) := by
  apply LightCondensed.hom_ext
  intro T
  ext x
  apply (ProjectiveGeneratorProof.zdiscSectionsEquiv T.unop).injective
  let y := (((MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).mapIso
    internalDualPIso.symm.op).hom.hom.app T) x
  change ProjectiveGeneratorProof.zdiscSectionsEquiv T.unop
      ((((internalDualFinsuppIsoProduct ℕ).hom ≫
        Limits.Pi.π (fun _ : ℕ => IntProof.Zdisc) i).hom.app T) y) = _
  rw [internalDualFinsuppIsoProduct_hom_apply_coord]
  rw [internalDualDiscreteSectionsEquiv_apply_basis]
  let D := (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ IntProof.SeqZ)
  let d := discreteGlobalElement (ModuleCat.of ℤ IntProof.SeqZ) (Finsupp.single i 1)
  let ψ := ProjectiveGeneratorProof.basisMap ≫ ProjectiveGeneratorProof.boundedCoord i
  let p := (MonoidalClosed.pre internalDualPIso.inv).app IntProof.Zdisc
  let evd : internalDual D ⟶ IntProof.Zdisc :=
    (λ_ (internalDual D)).inv ≫ (d ▷ internalDual D) ≫
      (ihom.ev D).app IntProof.Zdisc
  have hy : y = p.hom.app T x := rfl
  rw [hy]
  change ProjectiveGeneratorProof.zdiscSectionsEquiv T.unop
      ((p ≫ evd).hom.app T x) =
    ProjectiveGeneratorProof.zdiscSectionsEquiv T.unop
      ((doubleDualCoordinate ψ).hom.app T x)
  rw [show p ≫ evd =
      (λ_ (internalDual (internalDual (P ℤ)))).inv ≫
        ((d ≫ internalDualPIso.inv) ▷ internalDual (internalDual (P ℤ))) ≫
          (ihom.ev (internalDual (P ℤ))).app IntProof.Zdisc by
    exact pre_comp_evaluationAtGlobal internalDualPIso.inv d]
  rw [discreteGlobalElement_internalDualPIso_inv]
  rfl

/-- The explicit double-dual evaluation of `P ℤ` is the standard basis map into the product of
integers. -/
lemma doubleDualEvaluation_P_comp_iso :
    doubleDualEvaluation (P ℤ) ≫ doubleInternalDualPIsoProduct.hom =
      ProjectiveGeneratorProof.basisMap ≫
        ProjectiveGeneratorProof.boundedToProduct ≫
          ProjectiveGeneratorProof.productIntLightIsoProductZdisc.hom := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, doubleInternalDualPIsoProduct_hom_π]
  rw [doubleDualEvaluation_coordinate]
  dsimp only [ProjectiveGeneratorProof.boundedCoord]
  simp only [Category.assoc]

/-- Solidification inverts the double-dual evaluation map of `P ℤ`. -/
lemma isIso_solidification_map_doubleDualEvaluation_P :
    IsIso (solidification.map (doubleDualEvaluation (P ℤ))) := by
  let e := doubleInternalDualPIsoProduct.hom
  haveI : IsIso (solidification.map e) := by dsimp [e]; infer_instance
  haveI : IsIso
      (solidification.map (doubleDualEvaluation (P ℤ)) ≫ solidification.map e) := by
    rw [← Functor.map_comp, doubleDualEvaluation_P_comp_iso]
    simp only [Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (solidification.map (doubleDualEvaluation (P ℤ))) (solidification.map e)

/-- Internal duality with solid coefficients inverts the unit of solidification, by Day's
reflection theorem. -/
lemma isIso_internalDualMap_solidificationUnit (X : LightCondAb) :
    IsIso ((MonoidalClosed.pre (solidificationAdjunction.unit.app X)).app IntProof.Zdisc) := by
  have h₀ : ∀ (c : Solid) (d : LightCondAb),
      IsIso (solidificationAdjunction.unit.app
        ((ihom d).obj (isSolid.ι.obj c))) := by
    intro c d
    infer_instance
  have h₁ : ∀ (c : Solid) (d : LightCondAb),
      IsIso ((MonoidalClosed.pre (solidificationAdjunction.unit.app d)).app
        (isSolid.ι.obj c)) :=
    ((Monoidal.Reflective.isIso_tfae solidificationAdjunction).out 1 0).mpr h₀
  exact h₁ solidInteger X

/-- Double internal duality inverts the unit of solidification. -/
lemma isIso_doubleInternalDualMap_solidificationUnit (X : LightCondAb) :
    IsIso (doubleInternalDualMap (solidificationAdjunction.unit.app X)) := by
  haveI := isIso_internalDualMap_solidificationUnit X
  change IsIso ((MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).map
    (((MonoidalClosed.pre (solidificationAdjunction.unit.app X)).app
      IntProof.Zdisc).op))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The underlying solidification of `P ℤ` is reflexive after applying solidification. -/
lemma isIso_solidification_map_doubleDualEvaluation_solidP :
    IsIso (solidification.map
      (doubleDualEvaluation ((solidification ⋙ isSolid.ι).obj (P ℤ)))) := by
  let η := solidificationAdjunction.unit.app (P ℤ)
  haveI : IsIso (doubleInternalDualMap η) :=
    isIso_doubleInternalDualMap_solidificationUnit (P ℤ)
  haveI : IsIso (solidification.map η) := by infer_instance
  haveI : IsIso (solidification.map (doubleDualEvaluation (P ℤ))) :=
    isIso_solidification_map_doubleDualEvaluation_P
  haveI : IsIso (solidification.map
      (doubleDualEvaluation ((𝟭 LightCondAb).obj (P ℤ)))) := by
    simpa only [Functor.id_obj] using
      isIso_solidification_map_doubleDualEvaluation_P
  haveI : IsIso
      (solidification.map (doubleDualEvaluation ((𝟭 LightCondAb).obj (P ℤ))) ≫
        solidification.map (doubleInternalDualMap η)) := by
    infer_instance
  have hnat := doubleDualEvaluation_naturality η
  have hmap := congrArg (fun f => solidification.map f) hnat
  simp only [Functor.map_comp] at hmap
  haveI : IsIso
      (solidification.map η ≫ solidification.map
        (doubleDualEvaluation ((solidification ⋙ isSolid.ι).obj (P ℤ)))) := by
    rw [← hmap]
    infer_instance
  exact IsIso.of_isIso_comp_left (solidification.map η)
    (solidification.map
      (doubleDualEvaluation ((solidification ⋙ isSolid.ι).obj (P ℤ))))

/-- The underlying solidification of every free representable is reflexive after applying
solidification. -/
lemma isIso_solidification_map_doubleDualEvaluation_solidifiedFree (S : LightProfinite) :
    IsIso (solidification.map (doubleDualEvaluation
      ((solidification ⋙ isSolid.ι).obj ((free ℤ).obj S.toCondensed)))) := by
  let r := (ProjectiveGeneratorProof.solidifiedFreeRetractSolidP S).map isSolid.ι
  let h := (doubleDualEvaluationRetract r).map solidification
  exact (MorphismProperty.isomorphisms Solid).of_retract h
    isIso_solidification_map_doubleDualEvaluation_solidP

set_option backward.isDefEq.respectTransparency false in
/-- Solidification inverts the canonical map from a free representable to its double internal
dual. -/
lemma isIso_solidification_map_doubleDualCompletionMap (S : LightProfinite) :
    IsIso (solidification.map (doubleDualCompletionMap S)) := by
  let F := (free ℤ).obj S.toCondensed
  let η := solidificationAdjunction.unit.app F
  haveI : IsIso (doubleInternalDualMap η) :=
    isIso_doubleInternalDualMap_solidificationUnit F
  haveI : IsIso (solidification.map η) := by infer_instance
  haveI : IsIso (solidification.map
      (doubleDualEvaluation ((solidification ⋙ isSolid.ι).obj F))) :=
    isIso_solidification_map_doubleDualEvaluation_solidifiedFree S
  haveI : IsIso
      (solidification.map η ≫ solidification.map
        (doubleDualEvaluation ((solidification ⋙ isSolid.ι).obj F))) := by
    infer_instance
  have hnat := doubleDualEvaluation_naturality η
  have hmap := congrArg (fun f => solidification.map f) hnat
  simp only [Functor.map_comp] at hmap
  haveI : IsIso
      (solidification.map (doubleDualEvaluation ((𝟭 LightCondAb).obj F)) ≫
        solidification.map (doubleInternalDualMap η)) := by
    rw [hmap]
    infer_instance
  have hF : IsIso (solidification.map
      (doubleDualEvaluation ((𝟭 LightCondAb).obj F))) :=
    IsIso.of_isIso_comp_right
      (solidification.map (doubleDualEvaluation ((𝟭 LightCondAb).obj F)))
      (solidification.map (doubleInternalDualMap η))
  simpa only [doubleDualCompletionMap, Functor.id_obj] using hF

/-- The double-dual completion map is a local equivalence for the existing solidification. -/
lemma doubleDualCompletionMap_mem_isLocal (S : LightProfinite) :
    isSolid.isLocal (doubleDualCompletionMap S) := by
  intro A hA
  have hlocal : ObjectProperty.isLocal
      (fun X : LightCondAb => X ∈ Set.range isSolid.ι.obj) (doubleDualCompletionMap S) :=
    (ObjectProperty.isLocal_iff_isIso_map solidificationAdjunction
      (doubleDualCompletionMap S)).2
        (isIso_solidification_map_doubleDualCompletionMap S)
  exact hlocal A ⟨⟨A, hA⟩, rfl⟩

/-- The existing notion of solidity implies the double-dual extension condition. -/
lemma doubleDualExtensionProperty_of_isSolid (A : LightCondAb) (hA : isSolid A) :
    doubleDualExtensionProperty A := by
  intro S
  exact doubleDualCompletionMap_mem_isLocal S A hA

set_option backward.isDefEq.respectTransparency false in
/-- Internal duality sends every local equivalence for the existing solidification to an
isomorphism. -/
lemma isIso_internalDualMap_of_isLocal {X Y : LightCondAb} (f : X ⟶ Y)
    (hf : isSolid.isLocal f) :
    IsIso ((MonoidalClosed.pre f).app IntProof.Zdisc) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))]
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rcases T with ⟨T⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective
    (((MonoidalClosed.pre f).app IntProof.Zdisc).hom.app ⟨T⟩)
  let eY := ihomPoints ℤ Y IntProof.Zdisc T
  let eX := ihomPoints ℤ X IntProof.Zdisc T
  let m := (((MonoidalClosed.pre f).app IntProof.Zdisc).hom.app ⟨T⟩)
  let p := fun g : Y ⊗ (free ℤ).obj T.toCondensed ⟶ IntProof.Zdisc =>
    (f ▷ (free ℤ).obj T.toCondensed) ≫ g
  have hp : Function.Bijective p :=
    (isSolid.isLocal.whiskerRight_mem f hf ((free ℤ).obj T.toCondensed))
      IntProof.Zdisc isSolid_int
  have hcompat : ∀ x, eX (m x) = p (eY x) := by
    intro x
    exact IntProof.ihomPoints_pre_app f T x
  constructor
  · intro x y hxy
    apply eY.injective
    apply hp.1
    rw [← hcompat, ← hcompat, hxy]
  · intro z
    obtain ⟨g, hg⟩ := hp.2 (eX z)
    refine ⟨eY.symm g, ?_⟩
    apply eX.injective
    rw [hcompat, Equiv.apply_symm_apply, hg]

/-- Double internal duality sends local equivalences to isomorphisms. -/
lemma isIso_doubleInternalDualMap_of_isLocal {X Y : LightCondAb} (f : X ⟶ Y)
    (hf : isSolid.isLocal f) : IsIso (doubleInternalDualMap f) := by
  haveI := isIso_internalDualMap_of_isLocal f hf
  change IsIso ((MonoidalClosed.internalHom.flip.obj IntProof.Zdisc).map
    (((MonoidalClosed.pre f).app IntProof.Zdisc).op))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Bijectivity of precomposition is inherited by a retract of arrows. -/
lemma precomp_bijective_of_retractArrow {X Y Z W A : LightCondAb}
    {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
    (hg : Function.Bijective (fun k : W ⟶ A => g ≫ k)) :
    Function.Bijective (fun k : Y ⟶ A => f ≫ k) := by
  let iL : X ⟶ Z := h.i.left
  let iR : Y ⟶ W := h.i.right
  let rL : Z ⟶ X := h.r.left
  let rR : W ⟶ Y := h.r.right
  have hiw : iL ≫ g = f ≫ iR := h.i_w
  have hrw : rL ≫ f = g ≫ rR := h.r_w
  have hretL : iL ≫ rL = 𝟙 X := h.retract_left
  have hretR : iR ≫ rR = 𝟙 Y := h.retract_right
  constructor
  · intro a b hab
    change f ≫ a = f ≫ b at hab
    have hc : rR ≫ a = rR ≫ b := by
      apply hg.1
      calc
        g ≫ (rR ≫ a) = (g ≫ rR) ≫ a := (Category.assoc _ _ _).symm
        _ = (rL ≫ f) ≫ a := by rw [hrw]
        _ = rL ≫ (f ≫ a) := Category.assoc _ _ _
        _ = rL ≫ (f ≫ b) := by rw [hab]
        _ = (rL ≫ f) ≫ b := (Category.assoc _ _ _).symm
        _ = (g ≫ rR) ≫ b := by rw [hrw]
        _ = g ≫ (rR ≫ b) := Category.assoc _ _ _
    calc
      a = (iR ≫ rR) ≫ a := by rw [hretR, Category.id_comp]
      _ = iR ≫ (rR ≫ a) := by rw [Category.assoc]
      _ = iR ≫ (rR ≫ b) := by rw [hc]
      _ = (iR ≫ rR) ≫ b := by rw [Category.assoc]
      _ = b := by rw [hretR, Category.id_comp]
  · intro a
    obtain ⟨c, hc⟩ := hg.2 (rL ≫ a)
    refine ⟨iR ≫ c, ?_⟩
    change g ≫ c = rL ≫ a at hc
    calc
      f ≫ (iR ≫ c) = (f ≫ iR) ≫ c := (Category.assoc _ _ _).symm
      _ = (iL ≫ g) ≫ c := by rw [hiw]
      _ = iL ≫ (g ≫ c) := Category.assoc _ _ _
      _ = iL ≫ (rL ≫ a) := by rw [hc]
      _ = (iL ≫ rL) ≫ a := (Category.assoc _ _ _).symm
      _ = a := by rw [hretL, Category.id_comp]

/-- If evaluation into the double dual has the extension property and an endomorphism becomes an
isomorphism on double duals, then precomposition by that endomorphism is bijective. -/
lemma precomp_bijective_of_doubleDualEvaluation {X A : LightCondAb} (f : X ⟶ X)
    [IsIso (doubleInternalDualMap f)]
    (heval : Function.Bijective
      (fun k : doubleInternalDual X ⟶ A => doubleDualEvaluation X ≫ k)) :
    Function.Bijective (fun k : X ⟶ A => f ≫ k) := by
  constructor
  · intro a b hab
    obtain ⟨a', ha'⟩ := heval.2 a
    obtain ⟨b', hb'⟩ := heval.2 b
    have hev : doubleDualEvaluation X ≫ (doubleInternalDualMap f ≫ a') =
        doubleDualEvaluation X ≫ (doubleInternalDualMap f ≫ b') := by
      simp only [← Category.assoc]
      rw [doubleDualEvaluation_naturality]
      simpa only [Category.assoc, ha', hb'] using hab
    have hdual : doubleInternalDualMap f ≫ a' = doubleInternalDualMap f ≫ b' :=
      heval.1 hev
    have hab' : a' = b' := (cancel_epi (doubleInternalDualMap f)).1 hdual
    rw [← ha', ← hb', hab']
  · intro a
    obtain ⟨a', ha'⟩ := heval.2 a
    change doubleDualEvaluation X ≫ a' = a at ha'
    refine ⟨doubleDualEvaluation X ≫ inv (doubleInternalDualMap f) ≫ a', ?_⟩
    change f ≫ ((doubleDualEvaluation X ≫ inv (doubleInternalDualMap f)) ≫ a') = a
    calc
      f ≫ ((doubleDualEvaluation X ≫ inv (doubleInternalDualMap f)) ≫ a') =
          (f ≫ doubleDualEvaluation X) ≫ (inv (doubleInternalDualMap f) ≫ a') := by
            simp only [Category.assoc]
      _ = (doubleDualEvaluation X ≫ doubleInternalDualMap f) ≫
          (inv (doubleInternalDualMap f) ≫ a') := by
            rw [doubleDualEvaluation_naturality]
      _ = doubleDualEvaluation X ≫ a' := by simp only [Category.assoc,
        IsIso.hom_inv_id_assoc]
      _ = a := ha'

set_option backward.isDefEq.respectTransparency false in
/-- The double-dual extension condition implies the existing `oneMinusShift` definition of
solidity. -/
lemma isSolid_of_doubleDualExtensionProperty (A : LightCondAb)
    (hA : doubleDualExtensionProperty A) :
    isSolid A := by
  rw [isSolid]
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))]
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rcases T with ⟨T⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective
    ((((MonoidalClosed.pre (oneMinusShift ℤ)).app A).hom.app ⟨T⟩))
  let F := (free ℤ).obj T.toCondensed
  let f : P ℤ ⊗ F ⟶ P ℤ ⊗ F := (oneMinusShift ℤ) ▷ F
  let rTensor : Retract (P ℤ ⊗ F)
      ((free ℤ).obj (ℕ∪{∞}).toCondensed ⊗ F) :=
    { i := (P_retract ℤ).i ▷ F
      r := (P_retract ℤ).r ▷ F
      retract := by
        rw [← comp_whiskerRight, (P_retract ℤ).retract]
        simp }
  let r : Retract (P ℤ ⊗ F)
      ((free ℤ).obj (((ℕ∪{∞}) : LightProfinite) ⊗ T).toCondensed) :=
    rTensor.trans (Retract.ofIso (IntProof.freeTensorIsoInt (ℕ∪{∞}) T))
  have hevalY : Function.Bijective
      (fun k : doubleInternalDual
          ((free ℤ).obj (((ℕ∪{∞}) : LightProfinite) ⊗ T).toCondensed) ⟶ A =>
        doubleDualEvaluation
          ((free ℤ).obj (((ℕ∪{∞}) : LightProfinite) ⊗ T).toCondensed) ≫ k) := by
    exact hA (((ℕ∪{∞}) : LightProfinite) ⊗ T)
  have hevalX : Function.Bijective
      (fun k : doubleInternalDual (P ℤ ⊗ F) ⟶ A =>
        doubleDualEvaluation (P ℤ ⊗ F) ≫ k) :=
    precomp_bijective_of_retractArrow (doubleDualEvaluationRetract r) hevalY
  have hfLocal : isSolid.isLocal f := by
    exact isSolid.isLocal.whiskerRight_mem (oneMinusShift ℤ)
      ProjectiveGeneratorProof.oneMinusShift_mem_isLocal F
  letI : IsIso (doubleInternalDualMap f) :=
    isIso_doubleInternalDualMap_of_isLocal f hfLocal
  have hf : Function.Bijective (fun k : P ℤ ⊗ F ⟶ A => f ≫ k) :=
    precomp_bijective_of_doubleDualEvaluation f hevalX
  let e := ihomPoints ℤ (P ℤ) A T
  let m := ((((MonoidalClosed.pre (oneMinusShift ℤ)).app A).hom.app ⟨T⟩))
  have hcompat : ∀ x, e (m x) = f ≫ e x := by
    intro x
    exact IntProof.ihomPoints_pre_app (oneMinusShift ℤ) T x
  constructor
  · intro x y hxy
    apply e.injective
    apply hf.1
    change f ≫ e x = f ≫ e y
    rw [← hcompat, ← hcompat, hxy]
  · intro z
    obtain ⟨g, hg⟩ := hf.2 (e z)
    change f ≫ g = e z at hg
    refine ⟨e.symm g, ?_⟩
    apply e.injective
    rw [hcompat, Equiv.apply_symm_apply, hg]

/-- The double-dual extension condition is equivalent to the existing `oneMinusShift`
definition of solidity. -/
theorem doubleDualExtensionProperty_iff_isSolid (A : LightCondAb) :
    doubleDualExtensionProperty A ↔ isSolid A :=
  ⟨isSolid_of_doubleDualExtensionProperty A, doubleDualExtensionProperty_of_isSolid A⟩

/-- The right-Kan extension condition is equivalent to the existing `oneMinusShift` definition of
a solid light condensed abelian group. -/
theorem classicalIsSolid_iff_isSolid (A : LightCondAb) :
    classicalIsSolid A ↔ isSolid A :=
  (classicalIsSolid_iff_doubleDualExtensionProperty A).trans
    (doubleDualExtensionProperty_iff_isSolid A)

/-- The classical right-Kan extension property and the existing solidity property agree as
object properties. -/
theorem classicalIsSolid_eq_isSolid : classicalIsSolid = isSolid := by
  ext A
  exact classicalIsSolid_iff_isSolid A

end Classical
end Solid
end LightCondensed
