import Mathlib.CategoryTheory.Sites.Coherent.Equivalence
import Mathlib.Condensed.Light.Basic

universe v u w

open CategoryTheory

namespace LightCondensed

variable {C : Type u} [Category.{v} C]

instance : LocallySmall.{max v w} (LightCondensed.{w} C) := by
  erw [locallySmall_congr ((equivSmallModel LightProfinite.{w}).sheafCongrPrecoherent C)]
  infer_instance

example (A B : LightCondensed.{w} C) : Small.{max v w} (A ⟶ B) := LocallySmall.hom_small A B

end LightCondensed
