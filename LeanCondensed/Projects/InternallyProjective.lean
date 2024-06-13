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
import LeanCondensed.LightProfinite.Sequences
/-!

# Project: prove that `ℤ[ℕ∪{∞}]` is internally projective in light condensed abelian groups

-/

universe u

open CategoryTheory

section InternallyProjective

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

class InternallyProjective (P : C) : Prop where
  preserves_epi : (ihom P).PreservesEpimorphisms

end InternallyProjective

section MonoidalClosed

variable (R : Type u) [CommRing R] -- might need some more assumptions

open MonoidalCategory

/- This should be done in much greater generality for sheaf categories, or even reflective
subcategories satisfying some extra properties. -/
noncomputable instance : MonoidalCategory (LightCondMod.{u} R) where
  tensorObj A B := (presheafToSheaf _ _).obj (A.val ⊗ B.val)
  tensorHom α β := (presheafToSheaf _ _).map (α.val ⊗ β.val)
  whiskerLeft A _ _ β := (presheafToSheaf _ _).map (A.val ◁ β.val)
  whiskerRight α B := (presheafToSheaf _ _).map (α.val ▷ B.val)
  tensorUnit := sorry
  associator := sorry
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

open LightCondensed

def ihom_points (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) := sorry
-- We should have an `R`-module structure on `M ⟶ N` for condensed `R`-modules `M`, `N`.

end MonoidalClosed

namespace LightProfinite

instance (S : LightProfinite.{u}) : Injective S := sorry

end LightProfinite

namespace LightCondensed

open LightProfinite

variable (R : Type _) [CommRing R] -- might need some more assumptions

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], ∀ S : LightProfinite, sorry := sorry

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

end LightCondensed
