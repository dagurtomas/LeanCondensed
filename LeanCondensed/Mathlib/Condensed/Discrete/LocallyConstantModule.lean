import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Condensed.Module
import LeanCondensed.Mathlib.Topology.LocallyConstant.Algebra
import LeanCondensed.Mathlib.Condensed.Adjunctions
import LeanCondensed.Mathlib.Condensed.Discrete.LocallyConstant
import LeanCondensed.SheafHomForget

universe u

namespace Condensed.LocallyConstant

open CategoryTheory Limits Condensed LocallyConstant Opposite

variable (R : Type (u+1)) [Ring R]

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
def sigmaComparisonMod (X : CondensedMod R) {α : Type u} [Finite α] (σ : α → Type u)
    [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)] :
    X.val.obj ⟨(CompHaus.of ((a : α) × σ a))⟩ ⟶
      ModuleCat.of R (((a : α) → X.val.obj ⟨CompHaus.of (σ a)⟩)) where
  toFun := fun x a ↦ X.val.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x
  map_add' := by aesop
  map_smul' := by aesop

lemma sigmaComparisonMod_eq_sigmaComparison
    (X : CondensedMod R) {α : Type u} [Finite α] (σ : α → Type u)
      [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)] :
        (sigmaComparisonMod R X σ).toFun =
          sigmaComparison ((Condensed.forget R).obj X) σ :=
  rfl

instance (X : CondensedMod R) {α : Type u} [Finite α] (σ : α → Type u)
    [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)] :
    IsIso (sigmaComparisonMod R X σ) := sorry

lemma inv_sigmaComparisonMod_eq_sigmaComparison
    (X : CondensedMod R) {α : Type u} [Finite α] (σ : α → Type u)
      [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)] :
        (inv (sigmaComparisonMod R X σ)).toFun =
          inv (sigmaComparison ((Condensed.forget R).obj X) σ) := by
  apply IsIso.eq_inv_of_hom_inv_id (f := (sigmaComparison ((Condensed.forget R).obj X) σ))
  ext x
  dsimp
  rw [← sigmaComparisonMod_eq_sigmaComparison]
  change (_ ≫ inv (sigmaComparisonMod R X σ)) x = x
  simp


/-- The projection of the counit. -/
noncomputable def counitAppAppImageMod {S : CompHaus.{u}} {Y : CondensedMod.{u} R}
  (f : LocallyConstant S (Y.val.obj (op (CompHaus.of PUnit.{u+1})))) : (a : α f) → Y.val.obj ⟨CompHaus.of <| a.val⟩ :=
  fun a ↦ Y.val.map (IsTerminal.from CompHaus.isTerminalPUnit _).op a.image

noncomputable def counitAppAppMod (S : CompHaus.{u}) (Y : CondensedMod.{u} R) :
    ModuleCat.of R (LocallyConstant S (Y.val.obj (op (CompHaus.of PUnit.{u+1})))) ⟶
      Y.val.obj ⟨S⟩ where
  toFun f :=
    haveI : Finite (α f.toFun) := sorry
    haveI : ∀ a : α f.toFun, CompactSpace (σ f.toFun a) := sorry
    ((inv (sigmaComparisonMod R Y (σ f.toFun))) ≫ (Y.val.mapIso (sigmaIso f).op).inv)
    (counitAppAppImageMod R f)
  map_add' := sorry
  map_smul' := sorry

/--
The functor from the category of modules to presheaves of modules on `CompHaus` given by locally
constant maps.
-/
@[simps]
noncomputable -- `comapₗ` is still unnecessarily noncomputable
def functorToPresheavesMod : ModuleCat.{u+1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ LocallyConstant.comapₗ R f.unop }
  map f := {  app := fun S ↦ LocallyConstant.mapₗ R f }

/-- `Condensed.LocallyConstant.functorToPresheavesMod` lands in condensed modules. -/
@[simps]
noncomputable
def functorMod : ModuleCat.{u+1} R ⥤ CondensedMod.{u} R where
  obj X := {
    val := (functorToPresheavesMod R).obj X
    cond := by
      rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget _)]
      exact (functor.obj X).cond
  }
  map f := ⟨(functorToPresheavesMod R).map f⟩

noncomputable def counitMod : underlying (ModuleCat.{u+1} R) ⋙ functorMod R ⟶ 𝟭 _ where
  app X := by
    refine sheafForgetPromote _ (CategoryTheory.forget _)
      (counit.app ((Condensed.forget R).obj X)).val fun ⟨S⟩ ↦ ?_
    simp only [counit, Functor.comp_obj, underlying_obj, functorMod_obj_val, functorToPresheavesMod_obj_obj,
      Functor.id_obj, counitApp, functor_obj_val, ModuleCat.forget_map]
    refine ⟨counitAppAppMod R S X, ?_⟩
    ext f
    haveI : Finite (α f.toFun) := sorry
    haveI : ∀ a : α f.toFun, CompactSpace (σ f.toFun a) := sorry
    change _ = ((inv (sigmaComparisonMod R X (σ f.toFun))) ≫ (X.val.mapIso (sigmaIso f).op).inv)
      (counitAppAppImageMod R f)
    simp only [counitAppApp, forget, sheafCompose_obj_val, Functor.comp_obj, Functor.mapIso_inv,
      Iso.op_inv, Functor.comp_map, ModuleCat.forget_map, types_comp_apply,
      LocallyConstant.toFun_eq_coe, ModuleCat.coe_comp, Function.comp_apply]
    congr
    erw [← inv_sigmaComparisonMod_eq_sigmaComparison]
    rfl
  naturality X Y f := by
    have := counit.naturality ((forget R).map f)
    apply (Condensed.forget R).map_injective
    simp only [Functor.comp_obj, underlying_obj, Functor.id_obj, Functor.comp_map, underlying_map,
      counit_app, Functor.id_map] at this
    simp only [Functor.comp_obj, underlying_obj, Functor.id_obj, Functor.comp_map, underlying_map,
      counit_app, Functor.map_comp, Functor.id_map]
    convert this
    · apply Sheaf.hom_ext
      exact map_sheafForgetPromote
        (coherentTopology CompHaus.{u}) (CategoryTheory.forget (ModuleCat.{u+1} R)) _ _
    · apply Sheaf.hom_ext
      exact map_sheafForgetPromote
        (coherentTopology CompHaus.{u}) (CategoryTheory.forget (ModuleCat.{u+1} R)) _ _

/--
The unit of the adjunciton is given by mapping each element to the corresponding constant map.

-- TODO: promote `LocallyConstant.const` to linear map etc. like `comap` and `map`.
-/
@[simps]
noncomputable def unitMod : 𝟭 _ ⟶ functorMod R ⋙ underlying _ where
  app X := {
    toFun := fun x ↦ LocallyConstant.const _ x
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
  }

-- theorem locallyConstantAdjunctionMod_left_triangle (X : ModuleCat.{u+1} R) :
--     (functorToPresheavesMod R).map ((unitMod R).app X) ≫ ((counitMod R).app ((functorMod R).obj X)).val = 𝟙 ((functorToPresheavesMod R).obj X) := by
--   ext ⟨S⟩ (f : LocallyConstant _ X)
--   simp only [Functor.id_obj, Functor.comp_obj, underlying_obj, FunctorToTypes.comp, NatTrans.id_app,
--     functorToPresheaves_obj_obj, types_id_apply]
--   simp only [counit, counitApp_val_app]
--   apply locallyConstantCondensed_ext (X := functor.obj X) (Y := functor.obj X) (f.map (unit.app X))
--   intro a
--   erw [incl_of_counitAppApp]
--   simp only [functor_obj_val, functorToPresheaves_obj_obj, unop_op, Functor.id_obj, map_apply,
--     CompHaus.coe_of, counitAppAppImage, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
--   ext x
--   erw [← α.map_eq_image _ a x]
--   rfl

/--
`Condensed.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
@[simps! unit_app_apply counit_app_val_app]
noncomputable def adjunctionMod : functorMod R ⊣ underlying _ :=
  Adjunction.mkOfUnitCounit {
    unit := unitMod R
    counit := counitMod R
    left_triangle := by
      ext X
      apply (Condensed.forget R).map_injective
      have := adjunction.left_triangle
      rw [NatTrans.ext_iff] at this
      have := congrFun this ((CategoryTheory.forget _).obj X)
      simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, underlying_obj,
        functor_obj_val, functorToPresheaves_obj_obj, CompHaus.coe_of, whiskerRight_app,
        whiskerLeft_app, NatTrans.id_app] at this
      simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, underlying_obj,
        functorMod_obj_val, functorToPresheavesMod_obj_obj, CompHaus.coe_of, whiskerRight_app,
        Functor.associator_hom_app, whiskerLeft_app, Category.id_comp, Functor.map_comp,
        NatTrans.id_app', CategoryTheory.Functor.map_id]
      convert this
      simp only [counitMod, Functor.comp_obj, underlying_obj, Functor.id_obj, counit_app,
        functorMod_obj_val, functorToPresheavesMod_obj_obj, CompHaus.coe_of]
      simp only [forget, Functor.comp_obj, underlying_obj, functorMod_obj_val,
        functorToPresheavesMod_obj_obj, CompHaus.coe_of, Functor.id_obj, sheafCompose_obj_val,
        adjunction, Adjunction.mkOfUnitCounit]
      sorry
      -- refine map_sheafForgetPromote
      --   (coherentTopology CompHaus.{u}) (CategoryTheory.forget (ModuleCat.{u+1} R)) _ ?_
    right_triangle := by
      sorry
      -- ext X (x : X.val.obj _)
      -- simp only [Functor.comp_obj, Functor.id_obj, underlying_obj, counit, FunctorToTypes.comp,
      --   whiskerLeft_app, Functor.associator_inv_app, functor_obj_val, functorToPresheaves_obj_obj,
      --   types_id_apply, whiskerRight_app, underlying_map, counitApp_val_app, NatTrans.id_app']
      -- apply locallyConstantCondensed_ext (unit.app _ x)
      -- intro a
      -- erw [incl_of_counitAppApp]
      -- simp only [CompHaus.coe_of, unit, Functor.id_obj, coe_const, counitAppAppImage]
      -- have := α.map_eq_image _ a ⟨PUnit.unit, by
      --   simp [α.mem_iff_eq_image (a := a), ← α.map_preimage_eq_image]⟩
      -- erw [← this]
      -- simp only [unit, Functor.id_obj, coe_const, Function.const_apply]
      -- congr
       }
