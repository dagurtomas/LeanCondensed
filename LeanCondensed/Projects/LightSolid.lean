/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Projects.Proj
import LeanCondensed.Projects.Sequence
import LeanCondensed.Projects.AdjointFunctorTheorem
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Condensed.Light.Small
/-!

# Project: light solid abelian groups

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed

section MonoidalClosed

attribute [local instance] Types.instConcreteCategory Types.instFunLike

variable (R : Type u) [CommRing R]

variable (A : LightCondMod R) (S : LightProfinite)

instance (A : LightCondMod R) : PreservesColimits (tensorRight A) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight A)

instance : Linear R (LightCondMod R) := inferInstanceAs (Linear R (Sheaf _ _))

instance : MonoidalLinear R (LightCondMod R) := by sorry

def tensorCokerIso {A B C : LightCondMod R} (f : A ⟶ B) : cokernel f ⊗ C ≅ cokernel (f ▷ C) :=
  preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

end MonoidalClosed

namespace LightProfinite

def shift : ℕ∪{∞} ⟶ ℕ∪{∞} := ConcreteCategory.ofHom {
  toFun
    | ∞ => ∞
    | OnePoint.some n => (n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, Filter.tendsto_add_atTop_iff_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    refine ⟨sSup (Option.some ⁻¹' U)ᶜ + 1, fun n hn ↦ by
      simpa using notMem_of_csSup_lt (Nat.succ_le_iff.mp hn) (Set.Finite.bddAbove hU)⟩ }

end LightProfinite

namespace LightCondensed

variable (R : Type _) [CommRing R]
-- might need some more assumptions eventually, finite type over `ℤ`?

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) :=
  internallyProjective_free_natUnionInfty _

instance : InternallyProjective (P R) := .ofRetract (P_retract _)

variable (R : Type) [CommRing R]

example : Abelian (LightCondMod R) := by infer_instance

example (A B : LightCondMod R) : AddCommGroup (A ⟶ B) := by infer_instance

def oneMinusShift' : (free R).obj (ℕ∪{∞}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _  - (lightProfiniteToLightCondSet ⋙ free R).map LightProfinite.shift

def oneMinusShift : P R ⟶ P R := by
  refine P_homMk R _ (oneMinusShift' R) ?_ ≫ P_proj R
  rw [oneMinusShift', Preadditive.comp_sub]
  simp only [sub_eq_zero, P_map, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R]

/-- A light condensed abelian group `A` is *solid* if the identity minus the map induced by the
shift map `ℕ∪∞ → ℕ∪∞` is an isomorphism on internal homs into `A` -/
def isSolid : ObjectProperty LightCondAb :=
  fun A ↦ IsIso ((MonoidalClosed.pre (oneMinusShift ℤ)).app A)

/-- A light condensed abelian group `A` is *solid* if the identity minus the map induced by the
shift map `ℕ∪∞ → ℕ∪∞` is an isomorphism on internal homs into `A` -/
abbrev IsSolid (A : LightCondAb) := isSolid.Is A

abbrev Solid : Type _ := isSolid.FullSubcategory

-- structure Solid where
--   toLightCondAb : LightCondAb
--   [isSolid : IsSolid toLightCondAb]

namespace Solid

-- def of (A : LightCondAb) [IsSolid A] : Solid := ⟨A, inferInstance⟩

instance category : Category Solid := ObjectProperty.FullSubcategory.category _

lemma isSolid_int : isSolid ((discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) := sorry

instance : Inhabited Solid := ⟨((discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)), isSolid_int⟩

-- @[simps!]
-- def solidToCondensed : Solid ⥤ LightCondAb := isSolid.ι

-- def fullyFaithfulSolidToCondensed : solidToCondensed.FullyFaithful := isSolid.fullyFaithfulι

-- instance : solidToCondensed.Full := fullyFaithfulSolidToCondensed.full

-- instance : solidToCondensed.Faithful := fullyFaithfulSolidToCondensed.faithful

instance {C J : Type*} [Category* C] [Category* J] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X : C) : PreservesLimitsOfShape J (ihom X) where
  preservesLimit {K} := {
    preserves {c} hc := by
      refine ⟨?_⟩
      apply coyonedaJointlyReflectsLimits
      intro ⟨Y⟩
      change IsLimit <| (ihom X ⋙ coyoneda.obj _).mapCone _
      let i : ihom X ⋙ coyoneda.obj ⟨Y⟩ ≅ coyoneda.obj ⟨X ⊗ Y⟩ := by
        refine NatIso.ofComponents ?_ ?_
        · intro Z
          exact (ihom.adjunction _).homEquiv _ _ |>.symm.toIso
        · intro Z₁ Z₂ f
          ext
          simp only [op_tensorObj, Functor.flip_obj_obj, yoneda_obj_obj, unop_tensorObj,
            Functor.comp_obj, Functor.comp_map, Functor.flip_obj_map, curriedTensor_obj_obj,
            Equiv.toIso_hom, types_comp_apply, yoneda_map_app]
          erw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
          simp
      exact IsLimit.mapConeEquiv i.symm <| isLimitOfPreserves _ hc }

instance {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    (X : C) : PreservesLimits (ihom X) where

instance (J : Type) [SmallCategory J] : isSolid.IsClosedUnderLimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk
  intro A ⟨⟨F, π, hl⟩, h⟩
  let hl' := isLimitOfPreserves (ihom (P ℤ)) hl
  let α := F.whiskerLeft <| MonoidalClosed.pre (oneMinusShift ℤ)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    exact h j
  let c := (Cones.postcompose α).obj ((ihom (P ℤ)).mapCone ⟨A, π⟩)
  have : hl'.lift c = (MonoidalClosed.pre (oneMinusShift ℤ)).app A := by
    apply hl'.hom_ext
    intro j
    change _ ≫ ((ihom (P ℤ)).mapCone ⟨A, π⟩).π.app _ = _
    simp only [Functor.comp_obj, Functor.const_obj_obj, IsLimit.fac]
    simp only [Functor.mapCone_pt, Functor.mapCone_π_app]
    simp only [MonoidalClosed.pre, Cones.postcompose_obj_pt, Functor.mapCone_pt,
      Cones.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj, Functor.comp_obj,
      Functor.mapCone_π_app, Functor.whiskerLeft_app, conjugateEquiv_apply_app,
      curriedTensor_obj_obj, ihom.ihom_adjunction_unit, curriedTensor_map_app,
      ihom.ihom_adjunction_counit, ← Functor.map_comp, ihom.coev_naturality_assoc, Category.assoc,
      ← ihom.ev_naturality, Functor.id_obj, c, α]
    rw [← whisker_exchange_assoc]
  dsimp [isSolid]
  rw [← this]
  rw [← IsLimit.nonempty_isLimit_iff_isIso_lift]
  exact ⟨(IsLimit.postcomposeHomEquiv (asIso α) _).symm hl'⟩

instance (J : Type) [SmallCategory J] : isSolid.IsClosedUnderColimitsOfShape J := sorry

instance : CreatesLimitsOfSize.{0, 0} isSolid.ι where
  CreatesLimitsOfShape := createsLimitsOfShapeFullSubcategoryInclusion _ _

instance : HasColimitsOfSize.{0, 0} LightCondAb := by
  dsimp [LightCondAb, LightCondMod, LightCondensed]
  exact hasColimitsOfSizeShrink.{0, 0, 1, 0} _

instance : CreatesColimitsOfSize.{0, 0} isSolid.ι where
  CreatesColimitsOfShape := createsColimitsOfShapeFullSubcategoryInclusion _ _

instance : HasLimitsOfSize.{0, 0} Solid := hasLimits_of_hasLimits_createsLimits isSolid.ι

instance : HasColimitsOfSize.{0, 0} Solid :=
  hasColimits_of_hasColimits_createsColimits isSolid.ι

instance : Functor.IsAccessible.{0} isSolid.ι where
  exists_cardinal :=
    have := Cardinal.fact_isRegular_aleph0
    ⟨.aleph0, inferInstance, { preservesColimitOfShape := inferInstance }⟩

instance : LocallySmall.{0} LightCondAb where

instance : LocallySmall.{0} Solid := locallySmall_of_faithful isSolid.ι

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

end

-- TODO: define this property:
-- instance : PreservesExtensions (solidToCondensed R) := sorry

def solidification : LightCondAb ⥤ Solid :=
  isSolid.ι.leftAdjoint

def _root_.LightCondAb.solidify (A : LightCondAb) : Solid := solidification.obj A

def val (A : Solid) : LightCondAb := A.1 -- maybe unnecessary, `A.1` is fine.

def solidificationAdjunction : solidification ⊣ isSolid.ι := .ofIsRightAdjoint _

instance : solidification.IsLeftAdjoint := solidificationAdjunction.isLeftAdjoint

open MonoidalCategory

instance : solidification.IsLocalization isSolid.isLocal := by
  convert ObjectProperty.isLocalization_isLocal solidificationAdjunction
  ext A
  simp only [Set.mem_range, ObjectProperty.ι_obj]
  constructor
  · intro h
    refine ⟨⟨A, h⟩, rfl⟩
  · rintro ⟨A, rfl⟩
    exact A.property

def ihomHomEquiv {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X Y Z : C) : (X ⟶ ((ihom Y).obj Z)) ≃ (Y ⟶ ((ihom X).obj Z)) :=
  ((ihom.adjunction _).homEquiv _ _).symm.trans <|
    ((yoneda.obj Z).mapIso (β_ X Y).op).toEquiv.trans ((ihom.adjunction _).homEquiv _ _)

def ihomAdjunctionIso {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] (X Y Z : C) :
    (ihom (X ⊗ Y)).obj Z ≅ (ihom Y).obj ((ihom X).obj Z) := by
  suffices yoneda.obj ((ihom (X ⊗ Y)).obj Z) ≅ yoneda.obj ((ihom Y).obj ((ihom X).obj Z)) by
    exact Yoneda.fullyFaithful.preimageIso this
  refine NatIso.ofComponents ?_ ?_
  · intro W
    exact (((ihom.adjunction _).homEquiv _ _).symm.trans
      (((yoneda.obj Z).mapIso (α_ X Y W.unop).symm.op).toEquiv.trans
      ((ihom.adjunction _).homEquiv _ _))).trans ((ihom.adjunction _).homEquiv _ _) |>.toIso
  · intros
    ext
    simp only [yoneda_obj_obj, curriedTensor_obj_obj, op_tensorObj, Opposite.op_unop,
      unop_tensorObj, Iso.op_symm, op_associator, Iso.symm_symm_eq, Equiv.toIso_hom,
      Equiv.coe_trans, Iso.toEquiv_fun, Functor.mapIso_hom, types_comp_apply, yoneda_obj_map,
      Function.comp_apply, unop_hom_associator]
    erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
      Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    simp [← Functor.map_comp]

def ihomFlipIso {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X Y Z : C) :
    (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) := by
  refine (ihomAdjunctionIso _ _ _).symm ≪≫
    (MonoidalClosed.internalHom.flip.obj Z).mapIso (β_ X Y).op ≪≫ ihomAdjunctionIso _ _ _

set_option maxHeartbeats 400000 in
lemma isSolid_internalHom (A B : LightCondAb) (hB : isSolid B) : isSolid ((ihom A).obj B) := by
  dsimp [isSolid] at hB ⊢
  have : IsIso <| (ihomFlipIso A (P ℤ) B).inv ≫
    (MonoidalClosed.internalHom.obj ⟨A⟩).map ((MonoidalClosed.pre (oneMinusShift ℤ)).app B) ≫
    (ihomFlipIso A (P ℤ) B).hom := inferInstance
  convert this
  rw [Iso.eq_inv_comp]
  simp [ihomFlipIso, ihomAdjunctionIso]
  apply Yoneda.fullyFaithful.map_injective
  simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
  ext ⟨W⟩ g : 3
  simp only [yoneda_obj_obj, FunctorToTypes.comp, NatIso.ofComponents_inv_app, Equiv.toIso_inv,
    Equiv.symm_trans_apply, Equiv.symm_symm, Iso.toEquiv_symm_fun, Functor.mapIso_inv,
    yoneda_obj_map, unop_tensorObj, unop_inv_associator, yoneda_map_app,
    NatIso.ofComponents_hom_app, Equiv.toIso_hom, Equiv.trans_apply, Iso.toEquiv_fun,
    Functor.mapIso_hom, unop_hom_associator]
  erw [MonoidalClosed.homEquiv_apply_eq, MonoidalClosed.homEquiv_apply_eq,
    MonoidalClosed.homEquiv_apply_eq, MonoidalClosed.homEquiv_apply_eq,
    MonoidalClosed.homEquiv_apply_eq, MonoidalClosed.homEquiv_apply_eq,
    MonoidalClosed.homEquiv_symm_apply_eq, MonoidalClosed.homEquiv_symm_apply_eq,
    MonoidalClosed.homEquiv_symm_apply_eq, MonoidalClosed.homEquiv_symm_apply_eq,
    MonoidalClosed.homEquiv_symm_apply_eq, MonoidalClosed.homEquiv_symm_apply_eq]
  rw [curry_pre_app, curry_pre_app, curry_pre_app]
  simp only [uncurry_curry]
  congr
  simp [curry_eq, uncurry_eq]
  simp only [← Functor.map_comp]
  simp only [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
    ← associator_inv_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc (W := A), ← whisker_exchange]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right]
  rw [MonoidalCategory.comp_whiskerRight_assoc, associator_naturality_left_assoc,
    whisker_exchange_assoc]

instance : isSolid.isLocal.IsMonoidal := by
  apply MorphismProperty.IsMonoidal.mk'
  intro X₁ X₂ Y₁ Y₂ f g hf hg Z hZ
  have h₁ := (ihom.adjunction X₁).homEquiv Y₁ Z |>.symm.bijective
  have h₂ := (ihom.adjunction X₂).homEquiv Y₂ Z |>.bijective
  convert h₁.comp (Function.Bijective.comp (g := ?map) ?bij h₂)
  case map =>
    exact (fun x ↦ g ≫ x) ∘ ihomHomEquiv _ _ _ ∘ (fun x ↦ f ≫ x) ∘ ihomHomEquiv _ _ _
  case bij =>
    refine (hg _ (isSolid_internalHom _ _ hZ)).comp ((Equiv.bijective _).comp
      ((hf _ (isSolid_internalHom _ _ hZ)).comp (Equiv.bijective _)))
  ext1 x
  simp only [curriedTensor_obj_obj, ihomHomEquiv, op_tensorObj, yoneda_obj_obj, unop_tensorObj,
    op_braiding, Equiv.coe_trans, Iso.toEquiv_fun, Functor.mapIso_hom, Function.comp_apply,
    Equiv.symm_apply_apply, yoneda_obj_map, unop_hom_braiding]
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply,
    Adjunction.homEquiv_symm_apply]
  simp [tensorHom_def, whisker_exchange_assoc]

instance : MonoidalCategory Solid :=
  inferInstanceAs <| MonoidalCategory <| LocalizedMonoidal solidification isSolid.isLocal (.refl _)

instance : solidification.Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    solidification isSolid.isLocal (.refl _)).Monoidal

instance : SymmetricCategory Solid :=
  inferInstanceAs <| SymmetricCategory <| LocalizedMonoidal solidification isSolid.isLocal (.refl _)

instance : MonoidalClosed Solid :=
  Monoidal.Reflective.monoidalClosed solidificationAdjunction

instance : HasLimitsOfSize.{u, 0} Type := inferInstance

instance : Category.{0, 1} (ModuleCat R) := inferInstance

instance : SmallCategory.{1} (LightCondMod R) := inferInstance

variable (A : LightCondMod R)

instance : HasLimitsOfSize.{0, 0} (ModuleCat R) := inferInstance

instance : HasLimitsOfSize.{0, 0} (LightCondMod R) :=
  show (HasLimitsOfSize (Sheaf _ _)) from inferInstance

end Solid

end LightCondensed
