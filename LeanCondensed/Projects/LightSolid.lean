/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Condensed.Discrete.Basic
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import LeanCondensed.Projects.InternallyProjective
import LeanCondensed.Projects.LightProfiniteInjective
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
/-!

# Project: light solid abelian groups

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed

attribute [local instance] HasForget.instFunLike

section MonoidalClosed

variable (R : Type u) [CommRing R]

variable (A : LightCondMod R) (S : LightProfinite)

def ihom_points (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) := sorry
-- We should have an `R`-module structure on `M ⟶ N` for condensed `R`-modules `M`, `N`,
-- then this could be made an `≅`.
-- But it's probably not needed in this proof.
-- This equivalence follows from the adjunction.
-- This probably needs some naturality lemmas

def tensorFreeIso (X Y : LightCondSet.{u}) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⨯ Y) :=
  Functor.Monoidal.μIso (free R) X Y ≪≫ ((free R).mapIso
    ((ChosenFiniteProducts.product X Y).isLimit.conePointUniqueUpToIso (limit.isLimit (pair X Y))))

def tensorFreeIso' (S T : LightProfinite) :
    (free R).obj S.toCondensed ⊗ (free R).obj T.toCondensed ≅
      (free R).obj (S ⨯ T).toCondensed := tensorFreeIso R S.toCondensed T.toCondensed ≪≫
        (free R).mapIso (Limits.PreservesLimitPair.iso lightProfiniteToLightCondSet _ _).symm

instance (A : LightCondMod R) : PreservesColimits (tensorRight A) := by sorry

instance : MonoidalPreadditive (LightCondMod R) := by sorry

instance : Linear R (LightCondMod R) := by sorry

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
-- might need some more assumptions, finite type over `ℤ`?

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := sorry
-- It's the ← direction that's important in this proof
-- The proof of this should be completely formal, using the characterisation of epimorphisms in
-- light condensed abelian groups as locally surjective maps
-- (see the file `Epi/LightCondensed.lean`), and `ihom_points` above (together with some ).

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
  simp [one_minus_shift']
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
