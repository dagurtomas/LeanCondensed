/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.Basic
import LeanCondensed.Projects.InternallyProjective
/-!

# Project: light solid abelian groups

* Define the condensed abelian group / module called `P`. This is `ℤ[ℕ∪{∞}]/(∞)`, the light
  condensed abelian group "classifying null sequences".

* Define `shift : P ⟶ P`.

* Define the property of a light condensed abelian group `A` of being solid as the fact that the
  natural map of internal homs from `P` to `A` induced by `1 - shift` is an iso.

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits MonoidalClosed

namespace LightCondensed

def _root_.LightProfinite.shift : ℕ∪{∞} ⟶ ℕ∪{∞} where
  toFun
    | ∞ => ∞
    | OnePoint.some n => (n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, Filter.tendsto_add_atTop_iff_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    refine ⟨sSup (Option.some ⁻¹' U)ᶜ + 1, fun n hn ↦ by
      simpa using not_mem_of_csSup_lt (Nat.succ_le_iff.mp hn) (Set.Finite.bddAbove hU)⟩

variable (R : Type) [CommRing R]

example : Abelian (LightCondMod R) := by infer_instance

example (A B : LightCondMod R) : AddCommGroup (A ⟶ B) := by infer_instance

def one_minus_shift' : (free R).obj (ℕ∪{∞}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _  - (lightProfiniteToLightCondSet ⋙ free R).map LightProfinite.shift

def one_minus_shift : P R ⟶ P R := by
  refine P_homMk R _ (one_minus_shift' R) ?_ ≫ P_proj R
  simp [one_minus_shift']
  sorry

abbrev induced_from_one_minus_shift (A : LightCondMod R) :
    ((ihom (P R)).obj A) ⟶ ((ihom (P R)).obj A) :=
  (pre (one_minus_shift R)).app A

variable {R}

class IsSolid (A : LightCondMod R) : Prop where
  one_minus_shift_induces_iso : IsIso ((pre (one_minus_shift R)).app A)

variable (R) in
structure Solid where
  toLightCondMod : LightCondMod R
  [isSolid : IsSolid toLightCondMod]

namespace Solid

def of (A : LightCondMod R) [IsSolid A] : Solid R := ⟨A⟩

instance category : Category (Solid R) :=
  InducedCategory.category toLightCondMod

instance : IsSolid ((discrete (ModuleCat R)).obj (ModuleCat.of R R)) := sorry

instance : Inhabited (Solid R) := ⟨Solid.of ((discrete (ModuleCat R)).obj (ModuleCat.of R R))⟩

variable (R) in
@[simps!]
def solidToCondensed : Solid R ⥤ LightCondMod R :=
  inducedFunctor _

variable (R) in
def solidification : LightCondMod R ⥤ Solid R := sorry

def _root_.LightCondMod.solidify (A : LightCondMod R) : Solid R := (solidification R).obj A

def val (A : Solid R) : LightCondMod R := A.toLightCondMod -- maybe unnecessary, `A.1` is fine.

variable (R) in
def solidificationAdjunction : solidification R ⊣ solidToCondensed R := sorry

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
