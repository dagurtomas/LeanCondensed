import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Condensed.Adjunctions
import Mathlib.Condensed.Module
/-!
# Adjunctions regarding categories of condensed objects

This file shows that the forgetful functor from condensed modules to condensed sets has a
left adjoint, called the free condensed module on a condensed set.

-/

universe u

variable (R : Type _) [Ring R]

open CategoryTheory

namespace Condensed

/-- The forgetful functor from condensed abelian groups to condensed sets. -/
def forget : CondensedMod R ⥤ CondensedSet := sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free condensed abelian group* on a condensed set.
-/
noncomputable
def free : CondensedSet ⥤ CondensedMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def freeAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

-- TODO: PR general form of this for `sheafCompose`
instance : (Condensed.forget R).Faithful where
  map_injective h := by
    rw [Sheaf.Hom.ext_iff, NatTrans.ext_iff] at h
    apply Sheaf.hom_ext
    ext S x
    exact congrFun (congrFun h S) x

end Condensed
