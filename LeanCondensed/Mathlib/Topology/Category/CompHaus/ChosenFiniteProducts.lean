/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Mathlib.Topology.Category.LightProfinite.ChosenFiniteProducts
import Mathlib.Condensed.CartesianClosed
import Mathlib.Condensed.Functors
import Mathlib.Condensed.TopCatAdjunction
import Mathlib.Topology.Category.TopCat.ULift

universe u

open CategoryTheory Limits CompHausLike

noncomputable instance : CartesianMonoidalCategory CompHaus.{u} :=
  chosenFiniteProducts (fun _ _ => inferInstance)

@[simps!]
def compHausToTopU : CompHaus.{u} ⥤ TopCat.{u+1} := compHausToTop.{u} ⋙ TopCat.uliftFunctor.{u+1}

instance {J : Type u} [SmallCategory J] : PreservesLimitsOfShape J
    TopCat.uliftFunctor.{u+1, u} where
  preservesLimit {K} := {
    preserves hc := sorry }

instance {J : Type u} [SmallCategory J] : PreservesLimitsOfShape J
    compHausToTopU.{u} :=
  inferInstanceAs (PreservesLimitsOfShape J (_ ⋙ _))

instance {J : Type u} [SmallCategory J] : PreservesLimitsOfShape J
    compHausToCondensed.{u} := by
  have : Functor.IsRightAdjoint topCatToCondensedSet.{u} :=
    CondensedSet.topCatAdjunction.isRightAdjoint
  let i : compHausToCondensed.{u} ≅
      compHausToTopU.{u} ⋙ topCatToCondensedSet.{u} := by
    refine NatIso.ofComponents ?_ ?_
    · intro X
      refine (sheafToPresheaf _ _).preimageIso ?_
      refine NatIso.ofComponents ?_ ?_
      intro S
      · exact {
          hom := fun ⟨f⟩ ↦ ContinuousMap.comp ⟨fun a ↦ ⟨a⟩, by continuity⟩ f.hom
          inv f := ⟨TopCat.ofHom (ContinuousMap.comp ⟨fun ⟨a⟩ ↦ a, by continuity⟩ f)⟩
          hom_inv_id := rfl
          inv_hom_id := rfl }
      · aesop
    · intro X Y f
      apply (sheafToPresheaf _ _).map_injective
      simp only [sheafToPresheaf_obj, Functor.comp_obj, topCatToSheafCompHausLike_obj,
        TopCat.toSheafCompHausLike_val_obj, Functor.preimageIso_hom, Functor.map_comp,
        Functor.map_preimage, Functor.comp_map]
      ext
      simp
      rfl
  exact preservesLimitsOfShape_of_natIso i.symm

instance : PreservesLimitsOfSize.{u, u} compHausToCondensed.{u} where
  preservesLimitsOfShape := inferInstance

instance : PreservesFiniteLimits compHausToCondensed.{u} := by
  exact PreservesLimitsOfSize.preservesFiniteLimits compHausToCondensed

noncomputable instance : compHausToCondensed.Monoidal := by
  have : Nonempty compHausToCondensed.Monoidal := by
    rw [@Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts]
    infer_instance
  exact this.some
