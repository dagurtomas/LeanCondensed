/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Condensed.Module
import LeanCondensed.Mathlib.Condensed.Discrete.LocallyConstant

universe w u

open CategoryTheory Condensed

variable (C : Type w) [Category.{u+1} C] [HasWeakSheafify (coherentTopology CompHaus) C]
    {s : C ⥤ Type (u+1)} [s.ReflectsIsomorphisms] [(coherentTopology CompHaus).HasSheafCompose s]

-- We need the API being developed in #12332 to be able to assume that `s` preserves sheafification
-- Then the following should hold:

theorem isIso_unit : IsIso (discreteUnderlyingAdj C).unit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro X
  apply (config := { allowSynthFailures := true }) Functor.ReflectsIsomorphisms.reflects s
  have : IsIso ((discreteUnderlyingAdj (Type _)).unit.app (s.obj X)) := inferInstance
  sorry

variable (R : Type (u+1)) [Ring R]

theorem CondensedMod.isIso_unit : IsIso (discreteUnderlyingAdj (ModuleCat.{u+1} R)).unit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro X
  apply (config := { allowSynthFailures := true }) Functor.ReflectsIsomorphisms.reflects
    (CategoryTheory.forget _)
  have : IsIso ((discreteUnderlyingAdj (Type _)).unit.app ((CategoryTheory.forget _).obj X)) :=
    inferInstance
  sorry
