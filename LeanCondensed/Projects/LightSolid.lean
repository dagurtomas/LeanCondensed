/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.InternallyProjective
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

instance (A : LightCondMod R) : PreservesColimits (tensorRight A) := by
  sorry

instance : Linear R (LightCondMod R) := inferInstanceAs (Linear R (Sheaf _ _))

instance : MonoidalLinear R (LightCondMod R) := by sorry

def tensorCokerIso {A B C : LightCondMod R} (f : A ⟶ B) : cokernel f ⊗ C ≅ cokernel (f ▷ C) :=
  preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

end MonoidalClosed

namespace LightProfinite

def shift : ℕ∪{∞} ⟶ ℕ∪{∞} := TopCat.ofHom {
  toFun
    | ∞ => ∞
    | OnePoint.some n => (n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, Filter.tendsto_add_atTop_iff_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    refine ⟨sSup (Option.some ⁻¹' U)ᶜ + 1, fun n hn ↦ by
      simpa using not_mem_of_csSup_lt (Nat.succ_le_iff.mp hn) (Set.Finite.bddAbove hU)⟩ }

end LightProfinite

namespace LightCondensed

variable (R : Type _) [CommRing R]
-- might need some more assumptions eventually, finite type over `ℤ`?

def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map (TopCat.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

def P : LightCondMod R := cokernel (P_map R)

def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf

instance : InternallyProjective (P R) := by
  rw [internallyProjective_iff_tensor_condition]
  intro A B e he S g
  sorry

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

variable (R : Type) [CommRing R]

example : Abelian (LightCondMod R) := by infer_instance

example (A B : LightCondMod R) : AddCommGroup (A ⟶ B) := by infer_instance

def one_minus_shift' : (free R).obj (ℕ∪{∞}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _  - (lightProfiniteToLightCondSet ⋙ free R).map LightProfinite.shift

def one_minus_shift : P R ⟶ P R := by
  refine P_homMk R _ (one_minus_shift' R) ?_ ≫ P_proj R
  simp only [one_minus_shift', Functor.comp_obj, Functor.comp_map, Preadditive.comp_sub,
    Category.comp_id]
  sorry


abbrev induced_from_one_minus_shift (A : LightCondMod R) :
    ((ihom (P R)).obj A) ⟶ ((ihom (P R)).obj A) :=
  (pre (one_minus_shift R)).app A

variable {R : Type} [CommRing R]

/-- A light condensed `R`-module `A` is *solid* if the shift map `ℕ∪∞ → ℕ∪∞` induces an isomorphism
on internal homs into `A` -/
class IsSolid (A : LightCondMod R) : Prop where
  one_minus_shift_induces_iso : IsIso ((pre (one_minus_shift R)).app A)

structure Solid (R : Type) [CommRing R] where
  toLightCondMod : LightCondMod R
  [isSolid : IsSolid toLightCondMod]

namespace Solid

def of (A : LightCondMod R) [IsSolid A] : Solid R := ⟨A⟩

instance category : Category (Solid R) :=
  InducedCategory.category toLightCondMod

instance : IsSolid ((discrete (ModuleCat R)).obj (ModuleCat.of R R)) := sorry

instance : Inhabited (Solid R) := ⟨Solid.of ((discrete (ModuleCat R)).obj (ModuleCat.of R R))⟩

@[simps!]
def solidToCondensed (R : Type) [CommRing R] : Solid R ⥤ LightCondMod R :=
  inducedFunctor _

def solidification  (R : Type) [CommRing R] : LightCondMod R ⥤ Solid R := sorry

def _root_.LightCondMod.solidify (A : LightCondMod R) : Solid R := (solidification R).obj A

def val (A : Solid R) : LightCondMod R := A.toLightCondMod -- maybe unnecessary, `A.1` is fine.

def solidificationAdjunction (R : Type) [CommRing R] : solidification R ⊣ solidToCondensed R :=
  sorry

instance : (solidification R).IsLeftAdjoint := (solidificationAdjunction R).isLeftAdjoint

instance : (solidToCondensed R).IsRightAdjoint := (solidificationAdjunction R).isRightAdjoint

open MonoidalCategory

/- This is the monoidal structure on localized categories -/
instance : MonoidalCategory (Solid R) := sorry

instance : HasLimitsOfSize.{u, 0} Type := inferInstance

instance : Category.{0, 1} (ModuleCat R) := inferInstance

instance : SmallCategory.{1} (LightCondMod R) := inferInstance

variable (A : LightCondMod R)

instance : HasLimitsOfSize.{0, 0} (ModuleCat R) := inferInstance

instance : HasLimitsOfSize.{0, 0} (LightCondMod R) :=
  show (HasLimitsOfSize (Sheaf _ _)) from inferInstance

instance : HasLimitsOfSize.{0, 0} (Solid R) := sorry

instance : HasColimits (Solid R) := sorry

example : PreservesLimits (solidToCondensed R) := inferInstance

instance : PreservesColimits (solidToCondensed R) := sorry

-- TODO: define this property:
-- instance : PreservesExtensions (solidToCondensed R) := sorry

end Solid

end LightCondensed
#min_imports
