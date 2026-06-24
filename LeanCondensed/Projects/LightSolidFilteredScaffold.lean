/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Projects.Sequence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.IndYoneda
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Condensed.Light.InternallyProjective

/-!
# Scaffold for filtered colimits of internal homs out of `P`

This file is a proof scaffold for replacing the remaining gap in
`LightCondensed.Solid.preservesFilteredColimits_ihom_P`.

The planned route is:

1. filtered colimits in `LightCondAb` are computed pointwise;
2. the `T`-valued points of `ihom (P ℤ)` identify with ordinary homs out of
   `P ℤ ⊗ ℤ[T]`;
3. `P ℤ ⊗ ℤ[T]` is a cokernel, so ordinary homs out of it are a finite limit of ordinary
   hom functors out of the numerator and denominator;
4. those numerator/denominator hom functors reduce to point evaluations of filtered colimits.

The declarations below isolate the intended Lean interfaces before porting the proof back to
`LightSolid.lean`.
-/

noncomputable section

open CategoryTheory LightProfinite Limits LightCondensed MonoidalCategory MonoidalClosed Opposite
open CategoryTheory.Limits

namespace CategoryTheory
namespace Sheaf

variable {C : Type*} [Category C] {D : Type*} [Category D]
variable {J : GrothendieckTopology C} {I : Type*} [Category I]

/-- If presheaf-level colimit cocones of a fixed shape have sheaf colimit points, then the
forgetful functor from sheaves to presheaves creates colimits of that shape. -/
@[implicit_reducible]
noncomputable def createsColimitsOfShapeOfIsSheaf
    (h : ∀ (F : I ⥤ Sheaf J D) (c : Cocone (F ⋙ sheafToPresheaf J D)),
      IsColimit c → Presheaf.IsSheaf J c.pt) :
    CreatesColimitsOfShape I (sheafToPresheaf J D) where
  CreatesColimit {K} := createsColimitOfIsSheaf K (h K)

end Sheaf
end CategoryTheory

namespace LightCondensed
namespace LightSolidFilteredScaffold

/-- Evaluation of a light condensed abelian group at a light profinite set. -/
abbrev lightCondAbPoints (T : LightProfinite) : LightCondAb ⥤ ModuleCat ℤ :=
  sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ) ⋙
    (evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj (Opposite.op T)

/-- A pointwise filtered colimit of light condensed abelian groups is again a sheaf. -/
lemma isSheaf_pointwiseFilteredColimit_presheaf
    {I : Type} [SmallCategory I] [IsFiltered I] (F : I ⥤ LightCondAb) :
    Presheaf.IsSheaf (coherentTopology LightProfinite)
      (pointwiseCocone (F ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  constructor
  · apply +allowSynthFailures comp_preservesFiniteProducts
    have : ∀ (i : I), PreservesFiniteProducts ((F ⋙ sheafToPresheaf _ _).obj i) := fun i => by
      exact inferInstanceAs (PreservesFiniteProducts (F.obj i).obj)
    exact ⟨fun _ ↦ preservesLimitsOfShape_of_evaluation _ _ fun d ↦
      inferInstanceAs (PreservesLimitsOfShape _ ((F ⋙ sheafToPresheaf _ _).obj d))⟩
  · intro X B π hπ pb hpb
    let Fp := F ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    let G : WalkingParallelPair ⥤ I ⥤ ModuleCat ℤ :=
      parallelPair
        (Functor.whiskerLeft Fp
          ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map pb.fst.op))
        (Functor.whiskerLeft Fp
          ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map pb.snd.op))
    let K : Cone G := Fork.ofι
      (Functor.whiskerLeft Fp ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map π.op))
      (by
        ext i x
        change ModuleCat.Hom.hom ((F.obj i).obj.map π.op ≫
            (F.obj i).obj.map pb.fst.op) x =
          ModuleCat.Hom.hom ((F.obj i).obj.map π.op ≫
            (F.obj i).obj.map pb.snd.op) x
        simpa using congrArg
          (fun f : (F.obj i).obj.obj (Opposite.op B) ⟶
              (F.obj i).obj.obj (Opposite.op pb.pt) => ModuleCat.Hom.hom f x)
          (regularTopology.equalizerCondition_w (F.obj i).obj pb))
    have hK : IsLimit K := by
      apply evaluationJointlyReflectsLimits
      intro i
      let ii : G ⋙ (evaluation I (ModuleCat ℤ)).obj i ≅
          parallelPair ((F.obj i).obj.map pb.fst.op) ((F.obj i).obj.map pb.snd.op) :=
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)
      let e : (Cone.postcompose ii.hom).obj (((evaluation I (ModuleCat ℤ)).obj i).mapCone K) ≅
          Fork.ofι ((F.obj i).obj.map π.op)
            (regularTopology.equalizerCondition_w (F.obj i).obj pb) := by
        refine Cone.ext (Iso.refl _) ?_
        rintro (_ | _) <;> rfl
      have hsheaf := (F.obj i).property
      rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition] at hsheaf
      exact (IsLimit.equivOfNatIsoOfIso ii _ _ e).symm (hsheaf.2 π pb hpb).some
    have hcolim : IsLimit ((colim (J := I) (C := ModuleCat ℤ)).mapCone K) :=
      isLimitOfPreserves (colim (J := I) (C := ModuleCat ℤ)) hK
    refine ⟨?_⟩
    let i : parallelPair
        ((pointwiseCocone Fp).pt.map pb.fst.op)
        ((pointwiseCocone Fp).pt.map pb.snd.op) ≅ G ⋙ colim :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by rfl) (by rfl)
    let e : (Cone.postcompose i.hom).obj
        (Fork.ofι ((pointwiseCocone Fp).pt.map π.op)
          (regularTopology.equalizerCondition_w (pointwiseCocone Fp).pt pb)) ≅
        (colim (J := I) (C := ModuleCat ℤ)).mapCone K := by
      refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _)
      · change (pointwiseCocone Fp).pt.map π.op =
          colimMap (Functor.whiskerLeft Fp ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map π.op))
        rfl
      · change (pointwiseCocone Fp).pt.map π.op ≫ (pointwiseCocone Fp).pt.map pb.fst.op =
          colimMap (Functor.whiskerLeft Fp ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map π.op) ≫
            Functor.whiskerLeft Fp ((evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).map pb.fst.op))
        rw [← Functor.map_comp, ← Functor.whiskerLeft_comp, ← Functor.map_comp]
        rfl
    exact (IsLimit.equivOfNatIsoOfIso i _ _ e).symm hcolim

/-- The key pointwise-colimit input: a filtered presheaf colimit of light condensed abelian groups
is again a sheaf. -/
lemma isSheaf_filtered_colimit_presheaf
    {I : Type} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ LightCondAb)
    (c : Cocone (F ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)))
    (hc : IsColimit c) :
    Presheaf.IsSheaf (coherentTopology LightProfinite) c.pt := by
  let i : c.pt ≅ (pointwiseCocone (F ⋙ sheafToPresheaf
      (coherentTopology LightProfinite) (ModuleCat ℤ))).pt :=
    hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
  rw [Presheaf.isSheaf_of_iso_iff i]
  exact isSheaf_pointwiseFilteredColimit_presheaf F

/-- Filtered colimits of light condensed abelian groups are created by the presheaf-forgetful
functor. -/
@[implicit_reducible]
noncomputable def lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape
    (I : Type) [SmallCategory I] [IsFiltered I] :
    CreatesColimitsOfShape I
      (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) :=
  CategoryTheory.Sheaf.createsColimitsOfShapeOfIsSheaf (isSheaf_filtered_colimit_presheaf)

attribute [local instance] lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape

/-- Point evaluation preserves filtered colimits once filtered colimits are pointwise. -/
lemma lightCondAbPoints_preservesFilteredColimits (T : LightProfinite) :
    PreservesFilteredColimits (lightCondAbPoints T) := by
  refine ⟨fun J _ _ => ?_⟩
  letI : CreatesColimitsOfShape J
      (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) :=
    lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape J
  apply comp_preservesColimitsOfShape

/-- Ordinary homs out of a free light condensed module are point evaluations. -/
noncomputable def hom_free_lightProfinite_iso_points (S : LightProfinite) :
    coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj S.toCondensed)) ≅
      lightCondAbPoints S ⋙ CategoryTheory.forget (ModuleCat ℤ) ⋙ uliftFunctor.{1, 0} := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · exact Equiv.toIso ((((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed A).trans
      (coherentTopology LightProfinite).yonedaEquiv).trans Equiv.ulift.symm)
  · intro A B f
    ext g
    change ULift.up ((coherentTopology LightProfinite).yonedaEquiv
        (((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed B) (g ≫ f))) =
      ULift.up (((LightCondensed.forget ℤ).map f).hom.app (op S)
        ((coherentTopology LightProfinite).yonedaEquiv
          (((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed A) g)))
    congr 1

/-- Homs out of a free light condensed module preserve small filtered colimits. -/
lemma preservesFilteredColimits_hom_free_lightProfinite (S : LightProfinite) :
    PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj S.toCondensed))) := by
  refine ⟨fun J _ _ => ?_⟩
  letI : PreservesFilteredColimits (lightCondAbPoints S) :=
    lightCondAbPoints_preservesFilteredColimits S
  letI : PreservesColimitsOfShape J (lightCondAbPoints S) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  letI : PreservesColimitsOfShape J (CategoryTheory.forget (ModuleCat ℤ)) := by
    infer_instance
  letI : PreservesColimitsOfShape J uliftFunctor.{1, 0} := by
    infer_instance
  exact preservesColimitsOfShape_of_natIso (hom_free_lightProfinite_iso_points S).symm

/-- Homs out of a tensor product of two free light condensed modules preserve small filtered
colimits. -/
lemma preservesFilteredColimits_hom_free_tensor_free (S T : LightProfinite) :
    PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op
        ((LightCondensed.free ℤ).obj S.toCondensed ⊗
          (LightCondensed.free ℤ).obj T.toCondensed))) := by
  let e : (LightCondensed.free ℤ).obj S.toCondensed ⊗
        (LightCondensed.free ℤ).obj T.toCondensed ≅
      (LightCondensed.free ℤ).obj (S ⊗ T).toCondensed :=
    Functor.Monoidal.μIso (LightCondensed.free ℤ) S.toCondensed T.toCondensed ≪≫
      (LightCondensed.free ℤ).mapIso
        (Functor.Monoidal.μIso lightProfiniteToLightCondSet S T)
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj (S ⊗ T).toCondensed))) :=
    preservesFilteredColimits_hom_free_lightProfinite (S ⊗ T)
  refine ⟨fun J _ _ => ?_⟩
  letI : PreservesColimitsOfShape J
      (coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj (S ⊗ T).toCondensed))) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  exact preservesColimitsOfShape_of_natIso (coyoneda.mapIso e.op)

/-- The numerator after tensoring the presentation of `P` with `ℤ[T]`. -/
abbrev PNumeratorTensor (T : LightProfinite) : LightCondAb :=
  ((LightCondensed.free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗
    (LightCondensed.free ℤ).obj T.toCondensed

/-- The denominator after tensoring the presentation of `P` with `ℤ[T]`. -/
abbrev PDenominatorTensor (T : LightProfinite) : LightCondAb :=
  ((LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) ⊗
    (LightCondensed.free ℤ).obj T.toCondensed

lemma preservesFilteredColimits_hom_PNumeratorTensor (T : LightProfinite) :
    PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op (PNumeratorTensor T))) := by
  exact preservesFilteredColimits_hom_free_tensor_free _ _

lemma preservesFilteredColimits_hom_PDenominatorTensor (T : LightProfinite) :
    PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op (PDenominatorTensor T))) := by
  exact preservesFilteredColimits_hom_free_tensor_free _ _

-- Local copy of the cokernel/tensor isomorphism, avoiding an import cycle with `LightSolid`.
set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCokerIsoScaffold {A B C : LightCondAb} (f : A ⟶ B) :
    cokernel f ⊗ C ≅ cokernel (f ▷ C) := by
  letI : PreservesColimits (tensorRight C) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight C)
  exact preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

-- Small filtered colimits commute with finite limits in `Type 1`.
set_option backward.isDefEq.respectTransparency false in
lemma lim_preservesFilteredColimitsOfSize_type1 (K : Type) [SmallCategory K] [FinCategory K] :
    PreservesFilteredColimitsOfSize.{0, 0} (lim : (K ⥤ Type 1) ⥤ Type 1) := by
  refine ⟨fun J _ _ => ?_⟩
  constructor
  intro F
  haveI : IsIso (colimit.post F (lim : (K ⥤ Type 1) ⥤ Type 1)) := by
    rw [show colimit.post F (lim : (K ⥤ Type 1) ⥤ Type 1) =
        (HasColimit.isoOfNatIso (limitFlipIsoCompLim F).symm ≪≫ colimitLimitIso F.flip).hom by
      apply colimit.hom_ext
      intro j
      apply limit.hom_ext
      intro k
      rw [colimit.ι_post]
      simp only [Iso.trans_hom, Category.assoc]
      erw [HasColimit.isoOfNatIso_ι_hom_assoc]
      change lim.map (colimit.ι F j) ≫ limit.π (colimit F.flip.flip) k =
        (limitFlipIsoCompLim F).symm.hom.app j ≫
          (colimit.ι (limit F.flip) j ≫ (colimitLimitIso F.flip).hom ≫
            limit.π (colimit F.flip.flip) k)
      rw [ι_colimitLimitIso_limit_π (F.flip) j k]
      have hflip : (limitFlipIsoCompLim F).symm.hom.app j ≫ (limit.π F.flip k).app j =
          limit.π (F.obj j) k := by
        change (limitFlipIsoCompLim F).inv.app j ≫ (limit.π F.flip k).app j =
          limit.π (F.obj j) k
        rw [limitFlipIsoCompLim_inv_app]
        rw [Category.assoc]
        rw [limitObjIsoLimitCompEvaluation_inv_π_app]
        rw [HasLimit.isoOfNatIso_inv_π]
        rfl
      rw [← Category.assoc, hflip]
      change lim.map (colimit.ι F j) ≫ limit.π (colimit F) k =
        limit.π (F.obj j) k ≫ (colimit.ι F j).app k
      exact limMap_π (colimit.ι F j) k]
    infer_instance
  exact preservesColimit_of_isIso_post (lim : (K ⥤ Type 1) ⥤ Type 1) F

/-- If ordinary homs out of `X` and `Y` preserve small filtered colimits, then ordinary homs out
of a cokernel of `X ⟶ Y` preserve small filtered colimits.

Ordinary hom out of a cokernel is an equalizer of ordinary hom functors, and filtered colimits
commute with finite limits in `Type`. -/
lemma preservesFilteredColimits_hom_cokernel_of_preserves_hom {X Y : LightCondAb} (f : X ⟶ Y)
    [PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op X))]
    [PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op Y))] :
    PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (Opposite.op (cokernel f))) := by
  refine ⟨fun J _ _ => ?_⟩
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (lim : (WalkingParallelPairᵒᵖ ⥤ Type 1) ⥤ Type 1) :=
    lim_preservesFilteredColimitsOfSize_type1 WalkingParallelPairᵒᵖ
  letI : PreservesColimitsOfShape J (lim : (WalkingParallelPairᵒᵖ ⥤ Type 1) ⥤ Type 1) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  let H : WalkingParallelPairᵒᵖ ⥤ LightCondAb ⥤ Type 1 := (parallelPair f 0).op ⋙ coyoneda
  have hH : PreservesColimitsOfShape J H.flip := by
    apply preservesColimitsOfShape_of_evaluation
    intro i
    have hi : PreservesColimitsOfShape J (H.obj i) := by
      cases i using Opposite.rec
      rename_i i
      cases i
      · change PreservesColimitsOfShape J (coyoneda.obj (Opposite.op X))
        infer_instance
      · change PreservesColimitsOfShape J (coyoneda.obj (Opposite.op Y))
        infer_instance
    exact preservesColimitsOfShape_of_natIso (flipCompEvaluation H i).symm
  letI : PreservesColimitsOfShape J H.flip := hH
  have hlim : PreservesColimitsOfShape J (limit H) := by
    exact preservesColimitsOfShape_of_natIso (limitFlipIsoCompLim H.flip).symm
  letI : PreservesColimitsOfShape J (limit H) := hlim
  exact preservesColimitsOfShape_of_natIso
    (coyonedaOpColimitIsoLimitCoyoneda (parallelPair f 0)).symm

/-- Ordinary homs out of `P ℤ ⊗ ℤ[T]` preserve small filtered colimits. -/
lemma preservesFilteredColimits_hom_P_tensor_free (T : LightProfinite) :
    PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed))) := by
  have hden : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (PDenominatorTensor T))) :=
    preservesFilteredColimits_hom_PDenominatorTensor T
  have hnum : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (PNumeratorTensor T))) :=
    preservesFilteredColimits_hom_PNumeratorTensor T
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (PDenominatorTensor T))) := hden
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (PNumeratorTensor T))) := hnum
  let f : PDenominatorTensor T ⟶ PNumeratorTensor T :=
    (P_map ℤ) ▷ (LightCondensed.free ℤ).obj T.toCondensed
  have hcoker : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (cokernel f))) :=
    preservesFilteredColimits_hom_cokernel_of_preserves_hom f
  let e : P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed ≅ cokernel f :=
    tensorCokerIsoScaffold (P_map ℤ)
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (coyoneda.obj (Opposite.op (cokernel f))) := hcoker
  refine ⟨fun J _ _ => ?_⟩
  letI : PreservesColimitsOfShape J (coyoneda.obj (Opposite.op (cokernel f))) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  exact preservesColimitsOfShape_of_natIso (coyoneda.mapIso e.op)

/-- The `T`-valued points of `ihom (P ℤ)` are ordinary homs out of `P ℤ ⊗ ℤ[T]`. -/
noncomputable def ihomP_points_forget_iso (T : LightProfinite) :
    (ihom (P ℤ) ⋙ lightCondAbPoints T ⋙ CategoryTheory.forget (ModuleCat ℤ) ⋙
        uliftFunctor.{1, 0}) ≅
      coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed)) := by
  refine NatIso.ofComponents (fun A => ?_) ?_
  · exact Equiv.toIso (Equiv.ulift.trans (LightCondensed.ihomPoints ℤ (P ℤ) A T))
  · intro A B f
    ext x
    change LightCondensed.ihomPoints ℤ (P ℤ) B T
        ((((ihom (P ℤ)).map f).hom.app (op T)) x.down) =
      LightCondensed.ihomPoints ℤ (P ℤ) A T x.down ≫ f
    rw [LightCondensed.ihom_map_val_app]
    simp

/-- Reduction from pointwise ordinary hom preservation to internal hom preservation. -/
lemma preservesFilteredColimits_ihom_P_of_pointwise_hom
    (h : ∀ T : LightProfinite,
      PreservesFilteredColimitsOfSize.{0, 0}
        (coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed)))) :
    PreservesFilteredColimitsOfSize.{0, 0} (ihom (P ℤ)) := by
  refine ⟨fun J _ _ => ?_⟩
  letI : CreatesColimitsOfShape J
      (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) :=
    lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape J
  have hpresheaf : PreservesColimitsOfShape J
      (ihom (P ℤ) ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) := by
    apply preservesColimitsOfShape_of_evaluation
    intro T
    cases T with
    | op T =>
      have hpoints_forget : PreservesColimitsOfShape J
          ((ihom (P ℤ) ⋙ lightCondAbPoints T) ⋙
            CategoryTheory.forget (ModuleCat ℤ) ⋙ uliftFunctor.{1, 0}) := by
        letI : PreservesColimitsOfShape J
            (coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed))) :=
          PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
        exact preservesColimitsOfShape_of_natIso (ihomP_points_forget_iso T).symm
      letI : PreservesColimitsOfShape J
          ((ihom (P ℤ) ⋙ lightCondAbPoints T) ⋙
            CategoryTheory.forget (ModuleCat ℤ) ⋙ uliftFunctor.{1, 0}) := hpoints_forget
      exact preservesColimitsOfShape_of_reflects_of_preserves
        (F := ihom (P ℤ) ⋙ lightCondAbPoints T)
        (G := CategoryTheory.forget (ModuleCat ℤ) ⋙ uliftFunctor.{1, 0})
  letI : PreservesColimitsOfShape J
      (ihom (P ℤ) ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) := hpresheaf
  exact preservesColimitsOfShape_of_reflects_of_preserves (F := ihom (P ℤ))
    (G := sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))

/-- Final scaffold for the target lemma in `LightSolid.lean`. -/
lemma preservesFilteredColimits_ihom_P_scaffold :
    PreservesFilteredColimitsOfSize.{0, 0} (ihom (P ℤ)) := by
  exact preservesFilteredColimits_ihom_P_of_pointwise_hom
    (fun T => preservesFilteredColimits_hom_P_tensor_free T)

end LightSolidFilteredScaffold
end LightCondensed
