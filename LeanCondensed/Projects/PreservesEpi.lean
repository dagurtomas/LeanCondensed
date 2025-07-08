import Mathlib

import LeanCondensed.Mathlib.CategoryTheory.Functor.EpiMono
import LeanCondensed.Projects.LightProfiniteInjective


universe u v

open CategoryTheory Category Preadditive LightProfinite OnePoint Limits LightCondensed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

class InternallyProjective (P : C) : Prop where
  preserves_epi : (ihom P).PreservesEpimorphisms

namespace InternallyProjective

theorem ofRetract {X Y : C} (r : Retract Y X) (proj : InternallyProjective X)
    : InternallyProjective Y :=
  haveI : Retract (ihom Y) (ihom X) := {
    i := MonoidalClosed.pre r.r
    r := MonoidalClosed.pre r.i
    retract := by
      rw [←MonoidalClosed.pre_map, r.retract, MonoidalClosed.pre_id]
  }
  InternallyProjective.mk <| preservesEpi_ofRetract this proj.preserves_epi

end InternallyProjective

open LightCondensed

variable (R : Type _) [CommRing R]

instance : TotallyDisconnectedSpace PUnit := by
  have := TotallySeparatedSpace.of_discrete
  apply TotallySeparatedSpace.totallyDisconnectedSpace

def pt := LightProfinite.of PUnit.{1}

def ι : pt ⟶ ℕ∪{∞} := (TopCat.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

instance : Mono ι := (CompHausLike.mono_iff_injective ι).mpr fun _ _ ↦ congrFun rfl

instance : Nonempty pt := by
  unfold pt
  infer_instance

noncomputable def ι_SplitMono : SplitMono ι where
  retraction := ((injective_of_light (LightProfinite.of PUnit.{1})).factors (𝟙 pt) ι).choose
  id := ((injective_of_light pt).factors _ _).choose_spec

noncomputable def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map (TopCat.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

noncomputable def ιSplit : SplitMono (P_map R) := SplitMono.map ι_SplitMono (lightProfiniteToLightCondSet ⋙ (free R))

noncomputable def P : LightCondMod R := cokernel (P_map R)

noncomputable def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

noncomputable def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf

noncomputable def xyz := (Preadditive.homGroup _ _).sub (𝟙 (free R).obj (ℕ∪{∞}).toCondensed)  ((ιSplit R).retraction ≫ ((lightProfiniteToLightCondSet ⋙ free R).map ι))

lemma comp_zero : P_map R ≫ xyz R = 0 := by
    erw [
        Preadditive.comp_sub,
        comp_id,
        Functor.comp_map,
        SplitMono.id_assoc,
        sub_eq_zero
    ]
    rfl

instance P_proj_Epi : Epi (P_proj R) := by
  unfold P_proj
  rw [←coequalizer_as_cokernel]
  exact coequalizer.π_epi

noncomputable def πSplit : SplitEpi (P_proj R) where
  section_ := P_homMk R ((free R).obj (ℕ∪{∞}).toCondensed) (xyz R) (comp_zero _)
  id := by
    apply (P_proj_Epi R).left_cancellation
    erw [
      cokernel.π_desc_assoc,
      sub_comp,
      id_comp,
      assoc,
      cokernel.condition,
      HasZeroMorphisms.comp_zero,
      sub_zero
    ]

noncomputable def r : Retract (P R) ((free R).obj ℕ∪{∞}.toCondensed) where
  i := (πSplit R).section_
  r := P_proj R
  retract := (πSplit R).id

instance : MonoidalCategory (LightCondMod.{u} R) := sorry

instance : MonoidalClosed (LightCondMod.{u} R) := sorry

instance qwerty : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

theorem qwerty' : InternallyProjective (P R) := (qwerty _).ofRetract (r _)
