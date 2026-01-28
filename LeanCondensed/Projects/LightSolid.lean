/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Epi
import LeanCondensed.Projects.MonoidalLinear
import LeanCondensed.Mathlib.CategoryTheory.Functor.EpiMono
import LeanCondensed.Mathlib.Condensed.Light.Limits
import Mathlib.Condensed.Light.Monoidal
import Mathlib.CategoryTheory.Preadditive.Projective.Internal
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Projects.Proj
import LeanCondensed.Projects.Sequence
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

/-- A light condensed abelian group `A` is *solid* if the shift map `ℕ∪∞ → ℕ∪∞` induces an
isomorphism on internal homs into `A` -/
class IsSolid (A : LightCondAb) : Prop where
  oneMinusShift_induces_iso : IsIso ((MonoidalClosed.pre (oneMinusShift ℤ)).app A)

structure Solid where
  toLightCondAb : LightCondAb
  [isSolid : IsSolid toLightCondAb]

namespace Solid

def of (A : LightCondAb) [IsSolid A] : Solid := ⟨A⟩

instance category : Category Solid := InducedCategory.instCategory (F := toLightCondAb)

instance : IsSolid ((discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) := sorry

instance : Inhabited Solid := ⟨Solid.of ((discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))⟩

@[simps!]
def solidToCondensed : Solid ⥤ LightCondAb := inducedFunctor _

instance : HasLimitsOfSize.{0, 0} Solid := sorry

instance : HasColimitsOfSize.{0, 0} Solid := sorry

instance : PreservesLimitsOfSize.{0, 0} solidToCondensed := sorry

instance : PreservesColimitsOfSize.{0, 0} solidToCondensed := sorry

instance : LocallySmall.{0} Solid where
  hom_small X Y := sorry--inferInstanceAs (Small (X.1 ⟶ Y.1))

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

end

-- def solidToCondensed' : ShrinkHoms Solid ⥤ ShrinkHoms LightCondAb :=
--   inducedFunctor _

-- TODO: define this property:
-- instance : PreservesExtensions (solidToCondensed R) := sorry

instance : solidToCondensed.IsRightAdjoint := by sorry
  -- TODO: use construction of left adjoint for Bousfield localizations instead
  -- let i : solidToCondensed ≅ (ShrinkHoms.equivalence.{0} Solid).functor ⋙
  --     solidToCondensed' ⋙
  --     (ShrinkHoms.equivalence.{0} LightCondAb).inverse := by
  --   refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  --   intro X Y f
  --   simp only [solidToCondensed_obj, ShrinkHoms.equivalence_functor, ShrinkHoms.equivalence_inverse,
  --     Functor.comp_obj, ShrinkHoms.functor_obj, ShrinkHoms.inverse_obj,
  --     solidToCondensed_map, Iso.refl_hom, Category.comp_id, Functor.comp_map,
  --     ShrinkHoms.functor_map, ShrinkHoms.inverse_map, Category.id_comp]
  --   erw [Equiv.apply_symm_apply]
  -- have : HasLimits (ShrinkHoms Solid) :=
  --   Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence _).inverse
  -- have : HasLimits (ShrinkHoms LightCondAb) :=
  --   Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence _).inverse
  -- have : PreservesLimits solidToCondensed' := sorry
  -- have : solidToCondensed'.IsRightAdjoint := by
  --   apply isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  --   intro A
  --   sorry
  -- have : ((ShrinkHoms.equivalence.{0} Solid).functor ⋙
  --     inducedFunctor _ ⋙
  --     (ShrinkHoms.equivalence.{0} LightCondAb).inverse).IsRightAdjoint := by
  --   apply (config := {allowSynthFailures := true}) Functor.isRightAdjoint_comp
  --   apply (config := {allowSynthFailures := true}) Functor.isRightAdjoint_comp
  --   exact this
  -- apply Functor.isRightAdjoint_of_iso i.symm

def solidification : LightCondAb ⥤ Solid :=
  solidToCondensed.leftAdjoint

def _root_.LightCondAb.solidify (A : LightCondAb) : Solid := solidification.obj A

def val (A : Solid) : LightCondAb := A.toLightCondAb -- maybe unnecessary, `A.1` is fine.

def solidificationAdjunction : solidification ⊣ solidToCondensed := .ofIsRightAdjoint _

instance : solidification.IsLeftAdjoint := solidificationAdjunction.isLeftAdjoint

open MonoidalCategory

/- This is the monoidal structure on localized categories -/
instance : MonoidalCategory Solid := sorry

instance : HasLimitsOfSize.{u, 0} Type := inferInstance

instance : Category.{0, 1} (ModuleCat R) := inferInstance

instance : SmallCategory.{1} (LightCondMod R) := inferInstance

variable (A : LightCondMod R)

instance : HasLimitsOfSize.{0, 0} (ModuleCat R) := inferInstance

instance : HasLimitsOfSize.{0, 0} (LightCondMod R) :=
  show (HasLimitsOfSize (Sheaf _ _)) from inferInstance

end Solid

end LightCondensed
