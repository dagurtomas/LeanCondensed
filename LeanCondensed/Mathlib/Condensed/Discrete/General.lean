import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Condensed.Module
import LeanCondensed.Mathlib.Condensed.Discrete.LocallyConstant

universe w u

open CategoryTheory Condensed

variable (C : Type w) [Category.{u+1} C] [HasWeakSheafify (coherentTopology CompHaus) C]
    {s : C ⥤ Type (u+1)} [s.ReflectsIsomorphisms] [(coherentTopology CompHaus).HasSheafCompose s]

-- We need the API being developed in #12332 to be able to assume that `s` preserves sheafification
-- Then the following should hold:

theorem isIso_unit : IsIso (discrete_underlying_adj C).unit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro X
  apply (config := { allowSynthFailures := true }) Functor.ReflectsIsomorphisms.reflects s
  have : IsIso ((discrete_underlying_adj (Type _)).unit.app (s.obj X)) := inferInstance
  sorry

variable (R : Type (u+1)) [Ring R]

theorem CondensedMod.isIso_unit : IsIso (discrete_underlying_adj (ModuleCat.{u+1} R)).unit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro X
  apply (config := { allowSynthFailures := true }) Functor.ReflectsIsomorphisms.reflects
    (CategoryTheory.forget _)
  have : IsIso ((discrete_underlying_adj (Type _)).unit.app ((CategoryTheory.forget _).obj X)) :=
    inferInstance
  sorry
