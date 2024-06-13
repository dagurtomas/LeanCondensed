/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Monoidal
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

variable (R : Type u) [Ring R] -- might need some more assumptions

/- This should be done in much greater generality for sheaf categories, or even reflective
subcategories satisfying some extra properties. -/
instance : MonoidalCategory (LightCondMod.{u} R) := sorry

/- This should be done in much greater generality for sheaf categories, or even reflective
subcategories satisfying some extra properties. -/
instance : MonoidalClosed (LightCondMod.{u} R) := sorry

end MonoidalClosed

namespace LightProfinite

instance (S : LightProfinite.{u}) : Injective S := sorry

end LightProfinite

namespace LightCondensed

open LightProfinite

variable (R : Type) [Ring R] -- might need some more assumptions

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

end LightCondensed
