/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

This is analogous to the file `Profinite.AsLimit`.

-/

noncomputable section

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {c c' : Cone F}

@[simps]
def CategoryTheory.Limits.Cones.ptIsoOfIso (i : c ≅ c') : c.pt ≅ c'.pt where
  hom := i.hom.hom
  inv := i.inv.hom
  hom_inv_id := by simp [← Cone.category_comp_hom]
  inv_hom_id := by simp [← Cone.category_comp_hom]

namespace LightProfinite

universe u

variable (X : LightProfinite.{u})

-- TODO: move
instance : CountableCategory ℕ where

/-- The functor `ℕᵒᵖ ⥤ Fintype` whose limit is isomorphic to `X`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := X.toLightDiagram.diagram

/-- An abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := X.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
A cone over `X.diagram` whose cone point is isomorphic to `X`.
(Auxiliary definition, use `X.asLimitCone` instead.)
-/
def asLimitConeAux : Cone X.diagram :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).liftedCone

/-- An auxiliary isomorphism of cones used to prove that `X.asLimitConeAux` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone X.asLimitConeAux ≅ X.toLightDiagram.cone :=
  let c : Cone (X.diagram ⋙ lightToProfinite) := X.toLightDiagram.cone
  (CreatesLimit.lifts c X.toLightDiagram.isLimit).validLift

/--
`X.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `X.asLimit` instead.)
-/
def asLimitAux : IsLimit X.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone X.asLimitConeAux) :=
    X.toLightDiagram.isLimit.ofIsoLimit X.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A cone over `X.diagram` whose cone point is `X`. -/
def asLimitCone : Cone X.diagram where
  pt := X
  π := {
    app := fun n ↦ (lightToProfiniteFullyFaithful.preimageIso <|
      Cones.ptIsoOfIso X.isoMapCone).inv ≫ X.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, X.asLimitConeAux.w]; rfl }

/-- `X.asLimitCone` is indeed a limit cone. -/
def asLimit : IsLimit X.asLimitCone := X.asLimitAux.ofIsoLimit <|
  Cones.ext (lightToProfiniteFullyFaithful.preimageIso <|
    Cones.ptIsoOfIso X.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)

/-- A bundled version of `X.asLimitCone` and `X.asLimit`. -/
def lim : Limits.LimitCone X.diagram := ⟨X.asLimitCone, X.asLimit⟩

abbrev proj (n : ℕ) : X ⟶ X.diagram.obj ⟨n⟩ := X.asLimitCone.π.app ⟨n⟩

lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (X.proj n) =
    (lightToProfinite.obj X).asLimitCone.π.app _ := by
  sorry

lemma proj_surjective (n : ℕ) : Function.Surjective (X.proj n) := by
  change Function.Surjective (lightToProfinite.map (X.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _
