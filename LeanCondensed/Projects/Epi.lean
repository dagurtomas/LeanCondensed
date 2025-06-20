import Mathlib

import LeanCondensed.Mathlib.CategoryTheory.Countable
import LeanCondensed.Projects.Pullbacks

open Function CategoryTheory Limits Opposite

universe u

lemma surj_pullback' {X Y Z : LightProfinite.{u}} (f : X ⟶ Z) {g : Y ⟶ Z}
    (hf : Function.Surjective f) : Function.Surjective ↑(pullback.snd f g) := by
  intro y

  let point : LightProfinite.{u} := LightProfinite.of PUnit
  let point_map : point ⟶ Y := TopCat.ofHom ⟨fun _ ↦ y, continuous_const⟩

  rcases hf (g y) with ⟨z, hz⟩

  let point_map' : point ⟶ X := TopCat.ofHom ⟨fun _ ↦ z, continuous_const⟩

  use pullback.lift point_map' point_map (by ext; erw [hz]; rfl) PUnit.unit

  rw [←ConcreteCategory.comp_apply, pullback.lift_snd]
  rfl

instance surj_widePullback {J : Type*} (B : LightProfinite.{u}) (objs : J → LightProfinite)
  (arrows: (j : J) → (objs j ⟶ B)) (hepi : ∀ j, Epi (arrows j)) [HasWidePullback B objs arrows]
    : ∀ j, Epi (WidePullback.π arrows j) := by
  classical
  intro i
  simp [LightProfinite.epi_iff_surjective] at ⊢ hepi
  intro xi
  let point : LightProfinite.{u} := LightProfinite.of PUnit
  let base_pt : B := arrows i xi
  have choice : ∀ j, ∃ xj, arrows j xj = base_pt := fun j ↦ hepi j base_pt
  let point_maps : (j : J) → (point ⟶ objs j) := (fun j ↦
    if h : i = j then
      CompHausLike.ofHom _ (ContinuousMap.const point (h ▸ xi))
    else
      (CompHausLike.ofHom _ (ContinuousMap.const point (choice j).choose))
  )
  let lift : point ⟶ widePullback B objs arrows :=
    WidePullback.lift (CompHausLike.ofHom _ (ContinuousMap.const point base_pt)) point_maps
    (
      by
        intro j
        unfold point_maps
        by_cases h : i = j
        · simp only [↓reduceDIte]
          rw [dif_pos h]
          subst h
          rfl
        · rw [dif_neg h]
          ext x
          simp only [ConcreteCategory.comp_apply, CompHausLike.hom_ofHom, ContinuousMap.const_apply]
          exact (choice j).choose_spec
    )
  use lift PUnit.unit
  rw [←ConcreteCategory.comp_apply, WidePullback.lift_π]
  simp [point_maps]




instance : lightProfiniteToLightCondSet.PreservesEpimorphisms := {
  preserves f hf := (LightCondSet.epi_iff_locallySurjective_on_lightProfinite _).mpr
    fun _ g ↦
      ⟨
        pullback f g,
        pullback.snd _ _,
        surj_pullback' f ((LightProfinite.epi_iff_surjective f).mp hf),
        pullback.fst _ _,
        pullback.condition
      ⟩
}

lemma abc {A : Type u} {s : Set A} {x y : A} {px : x ∈ s} {py : y ∈ s} (h : (⟨x, px⟩ : s) = ⟨y, py⟩) : x = y
  := congr_arg (fun (a : s) ↦ (↑a : A)) h

noncomputable def regular {X Y : LightProfinite} (π : X ⟶ Y)
    : Cofork (lightProfiniteToLightCondSet.map <| pullback.fst π π) (lightProfiniteToLightCondSet.map <| pullback.snd π π) := Cofork.ofπ (lightProfiniteToLightCondSet.map <| π) (by
  rw [
    ←lightProfiniteToLightCondSet.map_comp,
    ←lightProfiniteToLightCondSet.map_comp,
    pullback.condition
  ])

def cfork {X Y : LightProfinite} (π : X ⟶ Y)
  := Cofork (lightProfiniteToLightCondSet.map (pullback.fst π π)) (lightProfiniteToLightCondSet.map (pullback.snd π π))

noncomputable def regularLiftElem {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
      (cone : cfork π) : cone.pt.val.obj (op Y)
    :=
  let fX := yonedaEquiv cone.π.val
  have : cone.pt.val.map (pullback.fst π π).op fX = cone.pt.val.map (pullback.snd π π).op fX := by
    have this : (lightProfiniteToLightCondSet.map (pullback.fst π π) ≫ cone.π).val = (yoneda.map (pullback.fst π π) ≫ cone.π.val) := rfl
    have this' : (lightProfiniteToLightCondSet.map (pullback.snd π π) ≫ cone.π).val = (yoneda.map (pullback.snd π π) ≫ cone.π.val) := rfl

    erw [
        yonedaEquiv_naturality (F := cone.pt.val) cone.π.val (pullback.fst π π),
        yonedaEquiv_naturality (F := cone.pt.val) cone.π.val (pullback.snd π π),
        ←this, ←this',
        cone.condition,
    ]
  (((LightCondensed.equalizerCondition cone.pt).bijective_mapToEqualizer_pullback _ _ _ π).surjective ⟨fX, this⟩).choose

private lemma cone_elem {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π)
    : cone.pt.val.map (pullback.fst π π).op (yonedaEquiv cone.π.val) = cone.pt.val.map (pullback.snd π π).op (yonedaEquiv cone.π.val) := by
  have this : (lightProfiniteToLightCondSet.map (pullback.fst π π) ≫ cone.π).val = (yoneda.map (pullback.fst π π) ≫ cone.π.val) := rfl
  have this' : (lightProfiniteToLightCondSet.map (pullback.snd π π) ≫ cone.π).val = (yoneda.map (pullback.snd π π) ≫ cone.π.val) := rfl
  erw [
      yonedaEquiv_naturality (F := cone.pt.val) cone.π.val (pullback.fst π π),
      yonedaEquiv_naturality (F := cone.pt.val) cone.π.val (pullback.snd π π),
      ←this, ←this',
      cone.condition,
  ]

noncomputable def regularLift {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π) : lightProfiniteToLightCondSet.obj Y ⟶ cone.pt
  := ⟨ yonedaEquiv.symm (regularLiftElem π cone) ⟩

private lemma regularLift_prop {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π)
    : regularTopology.MapToEqualizer cone.pt.val π (pullback.fst π π) (pullback.snd π π) pullback.condition (regularLiftElem π cone) = ⟨yonedaEquiv cone.π.val, cone_elem π cone⟩
  := (((LightCondensed.equalizerCondition cone.pt).bijective_mapToEqualizer_pullback _ _ _ π).surjective ⟨yonedaEquiv cone.π.val, cone_elem π cone⟩).choose_spec

lemma regularLift_comp {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π)
    : (regular π).π ≫ regularLift π cone = cone.π := by
  refine Sheaf.Hom.ext (yonedaEquiv.injective ?_)
  erw [←yonedaEquiv_naturality (F := cone.pt.val), Equiv.apply_symm_apply]
  exact abc (s := {x : cone.pt.val.obj (Opposite.op X) | cone.pt.val.map (pullback.fst π π).op x = cone.pt.val.map (pullback.snd π π).op x}) (regularLift_prop π cone)

lemma regularLift_unique {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π] (cone : cfork π)
      (m : (lightProfiniteToLightCondSet.obj Y) ⟶ cone.pt) (hm : (regular π).π ≫ m = cone.π)
    : m = regularLift π cone := by
  erw [Cofork.π_ofπ, ←regularLift_comp π cone] at hm
  exact Epi.left_cancellation _ _ hm

noncomputable abbrev regular_IsColimit {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
    : IsColimit (regular π)
  := Cofork.IsColimit.mk _ (regularLift π) (regularLift_comp π) (regularLift_unique π)

noncomputable abbrev regular_RegularEpi {X Y : LightProfinite} (π : X ⟶ Y) [EffectiveEpi π]
    : RegularEpi (lightProfiniteToLightCondSet.map π) where
  W := lightProfiniteToLightCondSet.obj (pullback π π)
  left := lightProfiniteToLightCondSet.map (pullback.fst π π)
  right := lightProfiniteToLightCondSet.map (pullback.snd π π)
  w := by
    rw [
      ←lightProfiniteToLightCondSet.map_comp,
      ←lightProfiniteToLightCondSet.map_comp,
      pullback.condition
    ]
  isColimit := regular_IsColimit π

instance : lightProfiniteToLightCondSet.PreservesEffectiveEpis where
  preserves π _ :=
    have : RegularEpi (lightProfiniteToLightCondSet.map π) := regular_RegularEpi π
    inferInstance
