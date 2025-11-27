/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
import Mathlib.Condensed.Light.Epi
import LeanCondensed.LightCondensed.Yoneda
import LeanCondensed.Mathlib.CategoryTheory.Functor.EpiMono
import LeanCondensed.Mathlib.Condensed.Light.Limits
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Mathlib.Topology.Category.LightProfinite.ChosenFiniteProducts
/-!

# Internal projectivity

This file defines internal projectivity and provides explicit characterizations of
internal projectivity in the category of light condensed modules over a commutative ring.

-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

section InternallyProjective

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

class InternallyProjective (P : C) : Prop where
  preserves_epi : (ihom P).PreservesEpimorphisms

theorem ofRetract {X Y : C} (r : Retract Y X) (proj : InternallyProjective X) :
    InternallyProjective Y :=
  haveI : Retract (ihom Y) (ihom X) := {
    i := MonoidalClosed.pre r.r
    r := MonoidalClosed.pre r.i
    retract := by
      rw [←MonoidalClosed.pre_map, r.retract, MonoidalClosed.pre_id] }
  haveI _ := proj.preserves_epi
  InternallyProjective.mk <| preservesEpi_ofRetract this

end InternallyProjective

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory
  MonoidalClosed Subcanonical Functor

section Condensed

attribute [local instance] Types.instConcreteCategory Types.instFunLike

variable (R : Type u) [CommRing R]

instance : (coherentTopology LightProfinite).HasSheafCompose (forget (ModuleCat.{u} R)) :=
  hasSheafCompose_of_preservesLimitsOfSize _

def ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :=
  (freeYoneda (ModuleCat.adj.{u} R) _ _).symm.trans ((ihom.adjunction A).homEquiv _ _).symm
-- We have an `R`-module structure on `M ⟶ N` for condensed `R`-modules `M`, `N`,
-- and this could be made an `≅`. But it's not needed in this proof.


lemma tensorLeft_obj (X Y : LightCondMod.{u} R) : (tensorLeft X).obj Y = X ⊗ Y := rfl

lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B) :
    ∀ x, ConcreteCategory.hom (((ihom P).map e).val.app ⟨S⟩) x =
        (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e) := by
  intro x
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints, freeYoneda]
  change ((((freeForgetAdjunction R).homEquiv S.toCondensed _).trans
            (Subcanonical.yoneda S ((LightCondensed.forget R).obj _))).symm.trans
      ((ihom.adjunction P).homEquiv _ _).symm)
    ((ConcreteCategory.hom (((ihom P).map e).val.app (Opposite.op S))) x) =
  ((((freeForgetAdjunction R).homEquiv S.toCondensed ((ihom P).obj B)).trans
            (Subcanonical.yoneda S ((LightCondensed.forget R).obj ((ihom P).obj B)))).symm.trans
      ((ihom.adjunction P).homEquiv ((free R).obj S.toCondensed) B).symm)
    (((((freeForgetAdjunction R).homEquiv S.toCondensed ((ihom P).obj B)).trans
                (Subcanonical.yoneda S ((LightCondensed.forget R).obj ((ihom P).obj B)))).symm.trans
          ((ihom.adjunction P).homEquiv ((free R).obj S.toCondensed) B).symm).symm
      (((((freeForgetAdjunction R).homEquiv S.toCondensed ((ihom P).obj A)).trans
                  (Subcanonical.yoneda S ((LightCondensed.forget R).obj ((ihom P).obj A)))).symm.trans
            ((ihom.adjunction P).homEquiv ((free R).obj S.toCondensed) A).symm)
          x ≫
        e))
  simp only [curriedTensor_obj_obj, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  erw [← Adjunction.homEquiv_naturality_right_symm]
  erw [← Adjunction.homEquiv_naturality_right_symm]
  simp only [Subcanonical.yoneda, sheafToPresheaf_obj, Equiv.symm_trans_apply,
    curriedTensor_obj_obj, EmbeddingLike.apply_eq_iff_eq]
  change (fullyFaithfulSheafToPresheaf _ _).homEquiv.symm _ = _ ≫ _
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  erw [Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.homEquiv_symm_apply]
  ext
  simp [yonedaEquiv]
  rfl

lemma ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : _ ⟶ _) :
    (ihomPoints R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ConcreteCategory.hom (((ihom P).obj B).val.map π.op) ((ihomPoints R P B S').symm f) := by
  simp only [ihomPoints, Equiv.symm_trans_apply, Equiv.symm_symm]
  simp only [freeYoneda, Subcanonical.yoneda, sheafToPresheaf_obj, Equiv.trans_apply]
  change ((fullyFaithfulSheafToPresheaf _ _).homEquiv.trans _)
    (((freeForgetAdjunction R).homEquiv _ _)
      (((ihom.adjunction P).homEquiv _ _) _)) = _
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
    Adjunction.homEquiv_apply]
  simp only [Functor.comp_obj, ihom.ihom_adjunction_unit, Functor.map_comp]
  simp only [← Functor.map_comp]
  rw [(ihom P).map_comp, ← ihom.coev_naturality_assoc]
  simp only [Functor.map_comp]
  rw [Adjunction.unit_naturality_assoc]
  erw [Equiv.trans_apply, Equiv.trans_apply, yonedaEquiv_comp,
    Functor.FullyFaithful.homEquiv_apply, yonedaEquiv_comp]
  simp only [comp_val, yonedaEquiv, yoneda_obj_obj, Opposite.op_unop, Equiv.coe_fn_mk,
    FunctorToTypes.comp]
  erw [← (((LightCondensed.forget R).map ((ihom P).map f)).val.naturality_apply π.op)]
  simp only [ConcreteCategory.hom]
  apply congrArg
  simp only [← FunctorToTypes.comp]
  erw [← ((LightCondensed.forget R).map ((ihom.coev P).app ((free R).obj
    S'.toCondensed))).val.naturality_apply]
  simp only [ConcreteCategory.hom, FunctorToTypes.comp]
  apply congrArg
  have : (lightProfiniteToLightCondSet.map π).val.app (Opposite.op S) (𝟙 S) =
      S'.toCondensed.val.map π.op (𝟙 S') := rfl
  rw [this]
  simp
  rfl

def tensorFreeIso (X Y : LightCondSet.{u}) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⨯ Y) :=
  Functor.Monoidal.μIso (free R) X Y ≪≫ ((free R).mapIso
    ((CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit (pair X Y))))

def tensorFreeIso' (S T : LightProfinite) :
    (free R).obj S.toCondensed ⊗ (free R).obj T.toCondensed ≅
      (free R).obj (S ⨯ T).toCondensed := tensorFreeIso R S.toCondensed T.toCondensed ≪≫
        (free R).mapIso (Limits.PreservesLimitPair.iso lightProfiniteToLightCondSet _ _).symm

namespace LightCondensed

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  constructor
  · intro ⟨h⟩ A B e he S g
    have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · intro h
    constructor
    constructor
    intro A B e he
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    erw [hh] at this
    simp [this]
    rfl

lemma internallyProjective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : (free R).obj S.toCondensed ⊗ P ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCondensed ⊗ P ⟶ A),
          (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

lemma free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (P ⊗ S.toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗  S'.toCondensed) ⟶ A),
            ((free R).map (P ◁ ((lightProfiniteToLightCondSet).map π))) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, Functor.OplaxMonoidal.δ_natural_right,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, ← Functor.LaxMonoidal.μ_natural_right, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (S.toCondensed ⊗ P) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S'.toCondensed ⊗ P) ⟶ A),
            ((free R).map (((lightProfiniteToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, Functor.OplaxMonoidal.δ_natural_left,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, ← Functor.LaxMonoidal.μ_natural_left, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((P ⊗ S).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗ S').toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.OplaxMonoidal.δ_natural_right,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      ← Functor.LaxMonoidal.μ_natural_right, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((S ⊗ P).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S' ⊗ P).toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.OplaxMonoidal.δ_natural_left,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      ← Functor.LaxMonoidal.μ_natural_left, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

end LightCondensed

end Condensed
