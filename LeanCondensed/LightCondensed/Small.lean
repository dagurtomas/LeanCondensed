/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Equivalence
import Mathlib.Condensed.Light.Module

universe v u w

open CategoryTheory Functor

namespace LightCondensed

variable {C : Type u} [Category.{v} C]

instance : LocallySmall.{max v w} (LightProfinite.{w}ᵒᵖ ⥤ C) := by
  rw [locallySmall_congr
    (Functor.asEquivalence (((whiskeringLeft _ _ _).obj (equivSmallModel _).op.inverse)))]
  infer_instance

instance : LocallySmall.{max v w} (LightCondensed.{w} C) := by
  erw [locallySmall_congr ((equivSmallModel LightProfinite.{w}).sheafCongrPrecoherent C)]
  infer_instance

example (A B : LightCondensed.{w} C) : Small.{max v w} (A ⟶ B) := inferInstance

example : LocallySmall.{u} LightCondSet.{u} := inferInstance

example (R : Type) [Ring R] : LocallySmall.{0} (LightCondMod R) := inferInstance

example : LocallySmall.{0} LightCondAb := inferInstance

end LightCondensed
