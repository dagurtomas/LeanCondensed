/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.TopCatAdjunction
import Mathlib.Topology.Compactness.PseudometrizableLindelof
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Spectral.Prespectral
import Mathlib.Topology.UniformSpace.DiscreteUniformity

universe u

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike.{u} P)
    (hP : HasProp P (X × Y))

def productCone : BinaryFan X Y :=
  BinaryFan.mk (P := CompHausLike.of P (X × Y))
    (TopCat.ofHom { toFun := Prod.fst }) (TopCat.ofHom { toFun := Prod.snd })

noncomputable def productIsLimit : IsLimit (productCone X Y hP) where
  lift := fun S : BinaryFan X Y => TopCat.ofHom {
    toFun := fun s => (S.fst s, S.snd s)
    continuous_toFun := by continuity }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    refine Prod.ext ?_ ?_
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h
      exact h

noncomputable def chosenFiniteProducts (hP : ∀ (X Y : CompHausLike.{u} P), HasProp P (X × Y))
    [HasProp P PUnit.{u + 1}] : CartesianMonoidalCategory (CompHausLike.{u} P) :=
  .ofChosenFiniteProducts
    ⟨_, CompHausLike.isTerminalPUnit⟩
    (fun X Y ↦ ⟨productCone X Y (hP X Y), productIsLimit X Y (hP X Y)⟩)

noncomputable instance : CartesianMonoidalCategory LightProfinite.{u} :=
  chosenFiniteProducts (fun _ _ => inferInstance)

example : LightProfinite ⥤ TopCat := by exact LightProfinite.toTopCat

instance {J : Type} [SmallCategory J] [CountableCategory J] : PreservesLimitsOfShape J
    lightProfiniteToLightCondSet.{u} := by
  have : Functor.IsRightAdjoint topCatToLightCondSet.{u} :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  haveI : PreservesLimitsOfShape J LightProfinite.toTopCat.{u} :=
    inferInstanceAs (PreservesLimitsOfShape J (lightToProfinite ⋙ Profinite.toTopCat))
  let i : lightProfiniteToLightCondSet.{u} ≅
      LightProfinite.toTopCat.{u} ⋙ topCatToLightCondSet.{u} := by
    refine NatIso.ofComponents ?_ ?_
    · intro X
      refine (sheafToPresheaf _ _).preimageIso ?_
      refine NatIso.ofComponents ?_ ?_
      intro S
      · exact {
          hom f := ⟨f.1, by continuity⟩
          inv f := TopCat.ofHom ⟨f.1, by continuity⟩
          hom_inv_id := rfl
          inv_hom_id := rfl }
      · aesop
    · intro X Y f
      apply (sheafToPresheaf _ _).map_injective
      simp only [sheafToPresheaf_obj, Functor.comp_obj, topCatToSheafCompHausLike_obj,
        TopCat.toSheafCompHausLike_val_obj, ContinuousMap.toFun_eq_coe, Functor.preimageIso_hom,
        Functor.map_comp, Functor.map_preimage, Functor.comp_map, compHausLikeToTop_map]
      ext S
      simp [lightProfiniteToLightCondSet, topCatToLightCondSet]
      rfl
  exact preservesLimitsOfShape_of_natIso i.symm

-- TODO: add this general instance (preserves countable => preserves finite)
instance : PreservesFiniteLimits lightProfiniteToLightCondSet.{u} where
  preservesFiniteLimits J :=
    haveI : CountableCategory J := inferInstance
    inferInstance

noncomputable instance : lightProfiniteToLightCondSet.Monoidal := by
  have : Nonempty lightProfiniteToLightCondSet.Monoidal := by
    rw [@Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts]
    infer_instance
  exact this.some
