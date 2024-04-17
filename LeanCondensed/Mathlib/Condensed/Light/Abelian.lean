/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LeftExact
import LeanCondensed.Mathlib.Condensed.Light.Basic

/-!

Light condensed abelian groups form an abelian category.

-/

universe u

open CategoryTheory Limits

-- TODO: change `CategoryTheory.sheafIsAbelian` to this statement.
instance CategoryTheory.sheafIsAbelian'
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {D : Type w} [Category.{w'} D] [Abelian D]
    [HasSheafify J D] [HasFiniteLimits (Sheaf J D)] : Abelian (Sheaf J D) := sorry

/--
The category of condensed abelian groups, defined as sheaves of abelian groups over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondensed.{u} AddCommGroupCat.{u}

noncomputable instance LightCondAb.abelian : Abelian LightCondAb.{u} :=
  letI : HasFiniteLimits <| Sheaf (coherentTopology LightProfinite.{u}) AddCommGroupCat.{u} :=
    hasFiniteLimits_of_hasLimitsOfSize _
  CategoryTheory.sheafIsAbelian' (J := coherentTopology LightProfinite.{u})
    (D := AddCommGroupCat.{u})
