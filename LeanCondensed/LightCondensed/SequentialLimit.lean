/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module
import LeanCondensed.Epi.LightCondensed
import LeanCondensed.LightCondensed.Yoneda
import LeanCondensed.LightProfinite.SequentialLimit
import LeanCondensed.Misc.NatFunctor
/-!

# Limits of epimorphisms in `LightCondMod R`

This file proves that a sequential limit of epimorhpisms is epimorphic in `LightCondMod R`
In other words, given epis
`⋯ ⟶ Sₙ₊₁ ⟶ Sₙ ⟶ ⋯ ⟶ S₀`,
the projection map `lim Sₙ ⟶ S₀` is surjective.
-/

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightCondensed

private noncomputable def preimage (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) :
    (n : ℕ) → ((T : LightProfinite) × (F.obj ⟨n⟩).val.obj ⟨T⟩)
  | 0 => ⟨S, g⟩
  | (n+1) =>
    have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
      (preimage R c hF S g n).1 (preimage R c hF S g n).2
    ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimage_transitionMap
  (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) :
    (n : ℕ) → ((preimage R c hF S g (n+1)).1 ⟶ (preimage R c hF S g n).1) := fun n ↦
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  this.choose_spec.choose

private lemma preimage_transitionMap_surj
  (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) (n : ℕ) :
    Function.Surjective (preimage_transitionMap R c hF S g n) :=
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  this.choose_spec.choose_spec.choose

private lemma preimage_w
  (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) (n : ℕ) :
      (F.map (homOfLE n.le_succ).op).val.app ⟨(LightCondensed.preimage R c hF S g (n+1)).1⟩
        (LightCondensed.preimage R c hF S g (n+1)).2 =
      ((F.obj ⟨n⟩).val.map (preimage_transitionMap R c hF S g n).op)
        (LightCondensed.preimage R c hF S g n).2 := by
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  exact this.choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimage_diagram
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) : ℕᵒᵖ ⥤ LightProfinite :=
  Nat.functor_mk (fun n ↦ (preimage R c hF S g n).1) fun n ↦ preimage_transitionMap R c hF S g n

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

lemma epi_limit_of_epi : Epi (c.π.app ⟨0⟩) := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro S g
  have h : Function.Surjective
      (limit.π (LightCondensed.preimage_diagram R c hF S g) { unop := 0 }) := by
    refine LightProfinite.limit_of_surjections_surjective (limit.isLimit _) ?_
    intro n
    simp only [preimage_diagram, Nat.succ_eq_add_one, Nat.functor_mk_obj, Nat.functor_mk_map_step]
    exact preimage_transitionMap_surj _ _ _ _ _ _
  refine ⟨limit (preimage_diagram R c hF S g), limit.π (preimage_diagram R c hF S g) ⟨0⟩, h, ?_⟩
  let g' := (LightCondensed.yoneda S ((forget R).obj (F.obj ⟨0⟩))).symm g
  let x : lightProfiniteToLightCondSet.obj (limit (preimage_diagram R c hF S g)) ⟶
      (forget R).obj c.pt := by
    let d : Cone F := by
      refine F.nat_op_cone_mk ((lightProfiniteToLightCondSet ⋙ free R).obj
        (limit (LightCondensed.preimage_diagram R c hF S g))) ?_ ?_
      · exact fun n ↦ (lightProfiniteToLightCondSet ⋙ free R).map
          (limit.π _ ⟨n⟩) ≫ (freeYoneda R _ _).symm (preimage R c hF S g n).2
      · intro n
        simp only [Functor.comp_obj, Functor.comp_map, Equiv.symm_trans_apply,
          Adjunction.homEquiv_counit, Functor.id_obj, Nat.succ_eq_add_one, Category.assoc]
        simp only [← Category.assoc, ← Functor.map_comp]
        sorry
    exact (freeForgetAdjunction R).homEquiv _ _ (hc.lift d)
  refine ⟨LightCondensed.yoneda _ _ x, ?_⟩
  simp only [Functor.const_obj_obj, yoneda_apply]
  erw [yonedaEquiv_apply]
  sorry

#exit

let d' : Cone (preimage_diagram R c hF S g ⋙ lightProfiniteToLightCondSet ⋙ free R) :=
      (lightProfiniteToLightCondSet ⋙ free R).mapCone (limit.cone _)
    let α' : preimage_diagram R c hF S g ⋙ lightProfiniteToLightCondSet ⟶ F ⋙ forget R := by
      fapply natTrans_nat_op_mk
      · exact fun n ↦ (yoneda _ _).symm (preimage R c hF S g n).2
      · intro n
        simp only [Nat.succ_eq_add_one, Functor.comp_obj, Functor.comp_map]
        apply Sheaf.hom_ext
        erw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_comp_val]
        ext T : 2
        simp only [NatTrans.comp_app]

        -- erw [yoneda_symm_apply_val_app]
        -- simp only [Nat.succ_eq_add_one, Functor.comp_obj, Functor.comp_map, Equiv.symm_trans_apply,
        --   sheafToPresheaf_obj]
        -- erw [Functor.FullyFaithful.homEquiv_symm_apply,
        --   Functor.FullyFaithful.homEquiv_symm_apply]
        -- apply (sheafToPresheaf _ _).map_injective
        -- simp [-sheafToPresheaf_obj, -sheafToPresheaf_map]
        -- simp
        -- ext T x
        -- simp only [FunctorToTypes.comp]
        -- erw [yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply]
        sorry

    let α : preimage_diagram R c hF S g ⋙ lightProfiniteToLightCondSet ⋙ free R ⟶ F := by
      fapply natTrans_nat_op_mk
      · exact fun n ↦ (freeYoneda R _ _).symm (preimage R c hF S g n).2
      · intro n
        apply Sheaf.hom_ext
        ext T : 2
        -- erw [← ((freeYoneda _ _ _).symm _).val.naturality]
        simp only [Nat.succ_eq_add_one, Functor.comp_obj, Functor.comp_map, Equiv.symm_trans_apply,
          sheafToPresheaf_obj, Adjunction.homEquiv_counit, Functor.id_obj, Category.assoc]
        sorry
        -- rw [← Adjunction.counit_naturality]
        -- simp only [Functor.id_obj, ← Category.assoc]
        -- congr 1
        -- simp only [← Functor.map_comp]
        -- congr 1
        -- apply (sheafToPresheaf _ _).map_injective
        -- erw [Functor.FullyFaithful.homEquiv_symm_apply,
        --   Functor.FullyFaithful.homEquiv_symm_apply]
        -- simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
        -- simp only [sheafToPresheaf_obj, sheafToPresheaf_map]
        -- -- ext T : 2
        -- -- simp only [NatTrans.comp_app]
        -- -- let xx := ((yonedaEquiv (F := preimage_diagram _ _ _ _ _)).symm (LightCondensed.preimage R c hF S g (n + 1)).snd)
        -- -- erw [← (yonedaEquiv.symm _).naturality]
        -- ext T x
        -- simp only [FunctorToTypes.comp]
        -- -- ext T : 2
        -- -- simp only [yonedaEquiv, yoneda_obj_obj, Opposite.op_unop, Equiv.coe_fn_symm_mk,
        -- --   NatTrans.comp_app]
        -- -- ext x
        -- -- simp?
        -- erw [yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply]
        -- have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF (n + 1))
        --   (preimage R c hF S g (n + 1)).1 (preimage R c hF S g (n + 1)).2
        -- have := this.choose_spec.choose_spec.choose_spec.choose_spec
        -- sorry
        -- -- change _ = ((F.obj ⟨n+1⟩).val.map (preimage_transitionMap R c hF S g (n + 1)).op)
        -- --     (LightCondensed.preimage R c hF S g (n + 1)).2 at this
        -- -- erw [this]
        -- -- simp only [Opposite.op_unop]
        -- -- sorry
    let d : Cone F := (Cones.postcompose α).obj d'
