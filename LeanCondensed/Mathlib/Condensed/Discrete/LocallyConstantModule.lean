import Mathlib.Condensed.Module
import LeanCondensed.Mathlib.Topology.LocallyConstant.Algebra
import LeanCondensed.Mathlib.Condensed.Discrete.LocallyConstant

universe u

namespace Condensed.LocallyConstant

open CategoryTheory Limits Condensed LocallyConstant Opposite

variable (R : Type (u+1)) [Ring R]

/--
The functor from the category of modules to presheaves of modules on `CompHaus` given by locally
constant maps.
-/
@[simps]
noncomputable -- `comapₗ` is still unnecessarily noncomputable
def functorToPresheavesMod : ModuleCat.{u+1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ LocallyConstant.comapₗ R f.unop }
  map f := {  app := fun S ↦ ModuleCat.asHom (LocallyConstant.mapₗ R f) }

/-- `Condensed.LocallyConstant.functorToPresheavesMod` lands in condensed modules. -/
@[simps]
noncomputable
def functorMod : ModuleCat.{u+1} R ⥤ CondensedMod.{u} R where
  obj X := {
    val := (functorToPresheavesMod R).obj X
    cond := by
      rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget _)]
      exact (functor.obj X).cond
  }
  map f := ⟨(functorToPresheavesMod R).map f⟩
