/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import LeanCondensed.LightCondensed.Yoneda
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Condensed.Light.Functors

open CategoryTheory Functor Opposite Limits Function GrothendieckTopology

universe u

variable {C : Type u} [Category C] {J : GrothendieckTopology C} [Subcanonical J]
  [HasFiniteCoproducts C] [∀ X : Sheaf J (Type _), PreservesFiniteProducts X.val]
  [HasWeakSheafify J (Type _)]

attribute [local instance] Types.instFunLike Types.instConcreteCategory

instance {n : ℕ} (S : Fin n → C) :
    PreservesColimit (Discrete.functor S) J.yoneda := by
  apply (config := { allowSynthFailures := true}) PreservesCoproduct.of_iso_comparison
  rw [isIso_iff_isIso_coyoneda_map]
  intro X
  rw [isIso_iff_bijective]
  have := instIsIsoPiComparison X.val (fun i ↦ ⟨S i⟩)

  let map : (J.yoneda.obj (∐ S) ⟶ X) → ((∐ fun i ↦ J.yoneda.obj (S i)) ⟶ X) :=
    (inv (piComparison (yoneda.obj X) (fun i ↦ ⟨J.yoneda.obj (S i)⟩)) ≫
      (yoneda.obj X).map (opCoproductIsoProduct fun i ↦ J.yoneda.obj (S i)).inv) ∘
      (Types.productIso (fun i ↦ J.yoneda.obj (S i) ⟶ X)).inv ∘
      (Pi.map (fun i ↦ (Subcanonical.yoneda (S i) X).symm)) ∘
      ((X.val.mapIso (opCoproductIsoProduct S)).hom ≫ (piComparison X.val (fun i ↦ ⟨S i⟩)) ≫
        (Types.productIso (fun i ↦ X.val.obj (op (S i)))).hom) ∘ (Subcanonical.yoneda (∐ S) X)

  have map_bij : Bijective map := by
    refine Bijective.comp ?_ (Bijective.comp ?_ (Bijective.comp ?_ (Bijective.comp ?_ ?_)))
    repeat {rw [←isIso_iff_bijective]; infer_instance}
    · exact Bijective.piMap (fun i ↦ (Subcanonical.yoneda _ _).symm.bijective)
    · rw [←isIso_iff_bijective]; infer_instance
    · exact (Subcanonical.yoneda _ _).bijective

  have : Injective ((CategoryTheory.yoneda.obj X).map
    (opCoproductIsoProduct fun i ↦ J.yoneda.obj (S i)).hom ≫
      (piComparison (yoneda.obj X) (fun i ↦ ⟨J.yoneda.obj (S i)⟩))) := by
    apply Bijective.injective
    rw [←isIso_iff_bijective]
    infer_instance

  suffices ((coyoneda.map (sigmaComparison J.yoneda S).op).app X) = map by
    rw [this]
    exact map_bij

  apply this.comp_left
  simp only [mapIso_hom, map]
  rw [← Function.comp_assoc]
  erw [← coe_comp (f := (inv (piComparison (yoneda.obj X) fun i ↦ ⟨J.yoneda.obj (S i)⟩) ≫
    (yoneda.obj X).map (opCoproductIsoProduct fun i ↦ J.yoneda.obj (S i)).inv))
    (g := ((yoneda.obj X).map (opCoproductIsoProduct fun i ↦ J.yoneda.obj (S i)).hom ≫
      piComparison (yoneda.obj X) fun i ↦ ⟨J.yoneda.obj (S i)⟩))]
  ext1 f
  ext1 ⟨i⟩
  simp only [yoneda_obj_obj, Discrete.functor_obj_eq_as, coyoneda_obj_obj, Function.comp_apply,
    coyoneda_map_app, Quiver.Hom.unop_op, types_comp_apply, yoneda_obj_map, Category.assoc,
    Iso.map_inv_hom_id_assoc, IsIso.inv_hom_id, Subcanonical.yoneda_apply, CategoryTheory.id_apply]

  change
    (piComparison
      (CategoryTheory.yoneda.obj X) (fun i ↦ ⟨J.yoneda.obj (S i)⟩) ≫
        Pi.π (fun i ↦ J.yoneda.obj (S i) ⟶ X) i)
      ((opCoproductIsoProduct fun i ↦ J.yoneda.obj (S i)).hom.unop ≫
        sigmaComparison J.yoneda S ≫ f) =
    ((Types.productIso fun i ↦ J.yoneda.obj (S i) ⟶ X).inv ≫
      Pi.π (fun i ↦ J.yoneda.obj (S i) ⟶ X) i) _

  erw [piComparison_comp_π (CategoryTheory.yoneda.obj X) (fun i ↦ ⟨J.yoneda.obj (S i)⟩)]
  rw [Types.productIso_inv_comp_π]
  simp only [Pi.map_apply, Types.productIso_hom_comp_eval_apply]

  change _ =
    (Subcanonical.yoneda (S i) X).symm (((X.val.map (opCoproductIsoProduct S).hom) ≫
      piComparison X.val (fun i ↦ ⟨S i⟩) ≫ Pi.π (fun i ↦ X.val.obj ⟨S i⟩) i)
      (Subcanonical.yoneda (∐ S) X f))
  rw [piComparison_comp_π, ← X.val.map_comp, opCoproductIsoProduct_hom_comp_π,
    yoneda_obj_map, ← unop_comp_assoc, opCoproductIsoProduct_hom_comp_π,
    Quiver.Hom.unop_op, ι_comp_sigmaComparison_assoc, ← Subcanonical.yoneda_symm_naturality,
    (Subcanonical.yoneda _ _).symm_apply_apply]

instance Subcanonical.preservesFiniteCoproductsYoneda :
    PreservesFiniteCoproducts J.yoneda where
  preserves n :=
    { preservesColimit {S} := by
        let i : S ≅ Discrete.functor (fun i ↦ S.obj ⟨i⟩) := Discrete.natIso (fun _ ↦ Iso.refl _)
        exact preservesColimit_of_iso_diagram J.yoneda i.symm
    }

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet := by
  apply (config := { allowSynthFailures := true}) Subcanonical.preservesFiniteCoproductsYoneda
  sorry
