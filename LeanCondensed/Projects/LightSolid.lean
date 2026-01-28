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

instance : PreservesLimitsOfSize.{0, 0} isSolid.ι := sorry

instance : PreservesColimitsOfSize.{0, 0} isSolid.ι := sorry

instance : HasLimitsOfSize.{0, 0} Solid := sorry

instance : HasColimitsOfSize.{0, 0} Solid := sorry

instance : Functor.IsAccessible.{0} isSolid.ι where
  exists_cardinal :=
    have := Cardinal.fact_isRegular_aleph0
    ⟨.aleph0, inferInstance, { preservesColimitOfShape := inferInstance }⟩

instance : LocallySmall.{0} LightCondAb where

instance : LocallySmall.{0} Solid where
  hom_small X Y := sorry--inferInstanceAs (Small (X.1 ⟶ Y.1))

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

end

-- TODO: define this property:
-- instance : PreservesExtensions (solidToCondensed R) := sorry

instance : isSolid.ι.IsRightAdjoint := by infer_instance

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

def ihomAdjunctionIso {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X Y Z : C) :
    (ihom (X ⊗ Y)).obj Z ≅ (ihom Y).obj ((ihom X).obj Z) := by
  sorry

def ihomFlipIso {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] (X Y Z : C) :
    (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) := by
  refine (ihomAdjunctionIso _ _ _).symm ≪≫
    (MonoidalClosed.internalHom.flip.obj Z).mapIso (β_ X Y).op ≪≫ ihomAdjunctionIso _ _ _

lemma isSolid_internalHom (A B : LightCondAb) (hB : isSolid B) : isSolid ((ihom A).obj B) := by
  sorry

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

/- This is the monoidal structure on localized categories -/
instance : MonoidalCategory Solid :=
  inferInstanceAs <| MonoidalCategory <| LocalizedMonoidal solidification isSolid.isLocal (.refl _)

instance : HasLimitsOfSize.{u, 0} Type := inferInstance

instance : Category.{0, 1} (ModuleCat R) := inferInstance

instance : SmallCategory.{1} (LightCondMod R) := inferInstance

variable (A : LightCondMod R)

instance : HasLimitsOfSize.{0, 0} (ModuleCat R) := inferInstance

instance : HasLimitsOfSize.{0, 0} (LightCondMod R) :=
  show (HasLimitsOfSize (Sheaf _ _)) from inferInstance

end Solid

end LightCondensed
