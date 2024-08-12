/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import LeanCondensed.LightCondensed.Yoneda
/-!

# Project: prove that `ℤ[ℕ∪{∞}]` is internally projective in light condensed abelian groups

-/

noncomputable section

universe u

open CategoryTheory LightProfinite MonoidalCategory OnePoint Limits LightCondensed

attribute [local instance] ConcreteCategory.instFunLike

section InternallyProjective

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

class InternallyProjective (P : C) : Prop where
  preserves_epi : (ihom P).PreservesEpimorphisms

end InternallyProjective

section MonoidalClosed

variable (R : Type u) [CommRing R] -- might need some more assumptions

/- This should be done in much greater generality for sheaf categories, or even reflective
subcategories satisfying some extra properties. -/
instance : MonoidalCategory (LightCondMod.{u} R) where
  tensorObj A B := (presheafToSheaf _ _).obj (A.val ⊗ B.val)
  tensorHom α β := (presheafToSheaf _ _).map (α.val ⊗ β.val)
  whiskerLeft A _ _ β := (presheafToSheaf _ _).map (A.val ◁ β.val)
  whiskerRight α B := (presheafToSheaf _ _).map (α.val ▷ B.val)
  tensorUnit := (presheafToSheaf _ _).obj tensorUnit
  associator X Y Z := sorry
  leftUnitor := sorry
  rightUnitor := sorry
  tensorHom_def := sorry
  tensor_id := sorry
  tensor_comp := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry

/- This should be done in much greater generality for sheaf categories, or even reflective
subcategories satisfying some extra properties. -/
instance : MonoidalClosed (LightCondMod.{u} R) := sorry

variable (A : LightCondMod R) (S : LightProfinite)

def ihom_points (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) := sorry
-- We should have an `R`-module structure on `M ⟶ N` for condensed `R`-modules `M`, `N`,
-- then this could be made an `≅`.
-- But it's probably not needed in this proof.
-- This equivalence follows from the adjunction.
-- This probably needs some naturality lemmas

def tensorFreeIso (X Y : LightCondSet.{u}) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⨯ Y) := sorry

def tensorFreeIso' (S T : LightProfinite) :
    (free R).obj S.toCondensed ⊗ (free R).obj T.toCondensed ≅
      (free R).obj (S ⨯ T).toCondensed := tensorFreeIso R S.toCondensed T.toCondensed ≪≫
        (free R).mapIso (Limits.PreservesLimitPair.iso lightProfiniteToLightCondSet _ _).symm

def tensorCokerIso {A B C : LightCondMod R} (f : A ⟶ B) : cokernel f ⊗ C ≅ cokernel (f ▷ C) :=
  sorry
-- In general the tensor product commutes with colimits

end MonoidalClosed

namespace LightProfinite

instance (S : LightProfinite.{u}) : Injective S := sorry

end LightProfinite

namespace LightCondensed

variable (R : Type _) [CommRing R] -- might need some more assumptions

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := sorry
-- It's the ← direction that's important in this proof
-- The proof of this should be completely formal, using the characterisation of epimorphisms in
-- light condensed abelian groups as locally surjective maps
-- (see the file `Epi/LightCondensed.lean`), and `ihom_points` above (together with some ).

def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map (⟨fun _ ↦ ∞, continuous_const⟩)

def P : LightCondMod R := cokernel (P_map R)

def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf

instance : InternallyProjective (P R) := by
  rw [internallyProjective_iff_tensor_condition]
  intro A B e he S g
  sorry

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

end LightCondensed
