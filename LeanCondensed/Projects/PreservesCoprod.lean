import Mathlib
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import LeanCondensed.LightCondensed.Yoneda

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  Topology Function

universe u

attribute [local instance] Types.instFunLike Types.instConcreteCategory

instance {n : ℕ} (S : Fin n → LightProfinite.{u}) :
    PreservesColimit (Discrete.functor S) lightProfiniteToLightCondSet.{u} := by
  have : HasColimitsOfSize.{u} (LightCondSet.{u}) :=
    inferInstanceAs (HasColimitsOfSize.{u} (Sheaf _ _))
  apply (config := { allowSynthFailures := true}) PreservesCoproduct.of_iso_comparison
  rw [isIso_iff_isIso_coyoneda_map] -- or maybe `rw [isIso_iff_coyoneda_map_bijective]`
  intro X
  rw [isIso_iff_bijective]
  have := instIsIsoPiComparison X.val (fun i ↦ ⟨S i⟩)

  let map : ((∐ S).toCondensed ⟶ X) → ((∐ fun i ↦ (S i).toCondensed) ⟶ X) :=
    (inv (piComparison (yoneda.obj X) (fun i ↦ ⟨(S i).toCondensed⟩))
      ≫ (CategoryTheory.yoneda.obj X).map (opCoproductIsoProduct fun i ↦ (S i).toCondensed).inv)
      ∘ (Types.productIso (fun i ↦ (S i).toCondensed ⟶ X)).inv
      ∘ (Pi.map (fun i ↦ (LightCondensed.yoneda (S i) X).symm))
      ∘ (
          (X.val.mapIso (opCoproductIsoProduct S)).hom
            ≫ (piComparison X.val (fun i ↦ ⟨S i⟩))
            ≫ (Types.productIso (fun i ↦ X.val.obj (op (S i)))).hom
        )
      ∘ (LightCondensed.yoneda (∐ S) X)

  have map_bij : Bijective map := by
    refine Bijective.comp ?_
      (
        Bijective.comp ?_
          (Bijective.comp ?_ (Bijective.comp ?_ ?_))
      )
    repeat {rw [←isIso_iff_bijective]; infer_instance}
    exact Bijective.piMap (fun i ↦ (LightCondensed.yoneda _ _).symm.bijective)
    rw [←isIso_iff_bijective]; infer_instance
    exact (LightCondensed.yoneda _ _).bijective

  have : Injective ((CategoryTheory.yoneda.obj X).map (opCoproductIsoProduct fun i ↦ (S i).toCondensed).hom
      ≫ (piComparison (yoneda.obj X) (fun i ↦ ⟨(S i).toCondensed⟩))) := by
    apply Bijective.injective
    rw [←isIso_iff_bijective]
    infer_instance

  have : ((coyoneda.map (sigmaComparison lightProfiniteToLightCondSet S).op).app X)
      = map := by
    apply this.comp_left
    simp only [Equiv.invFun_as_coe, mapIso_hom, map]
    rw [
        ←Function.comp_assoc,
    ]
    erw [
        ←coe_comp
          (f := (CategoryTheory.inv (piComparison (CategoryTheory.yoneda.obj X) fun i ↦ op (S i).toCondensed)
            ≫ (CategoryTheory.yoneda.obj X).map (opCoproductIsoProduct fun i ↦ (S i).toCondensed).inv))
          (g := ((CategoryTheory.yoneda.obj X).map (opCoproductIsoProduct fun i ↦ (S i).toCondensed).hom
            ≫ piComparison (CategoryTheory.yoneda.obj X) fun i ↦ op (S i).toCondensed)),
    ]
    ext1 f
    ext1 ⟨i⟩
    simp only [yoneda_obj_obj, Discrete.functor_obj_eq_as, coyoneda_obj_obj, Function.comp_apply,
      coyoneda_map_app, Quiver.Hom.unop_op, types_comp_apply, yoneda_obj_map, Category.assoc,
      Iso.map_inv_hom_id_assoc, IsIso.inv_hom_id, yoneda_apply, CategoryTheory.id_apply, map]

    change
      (
        piComparison (CategoryTheory.yoneda.obj X) (fun i ↦ ⟨(S i).toCondensed⟩)
          ≫ Pi.π (fun i ↦ (S i).toCondensed ⟶ X) i
      )
      (
        (opCoproductIsoProduct fun i ↦ (S i).toCondensed).hom.unop
          ≫ sigmaComparison lightProfiniteToLightCondSet S
          ≫ f
      ) =
      (
        (Types.productIso fun i ↦ (S i).toCondensed ⟶ X).inv
          ≫ Pi.π (fun i ↦ (S i).toCondensed ⟶ X) i
      ) _

    erw [piComparison_comp_π (CategoryTheory.yoneda.obj X) (fun i ↦ ⟨(S i).toCondensed⟩)]
    rw [Types.productIso_inv_comp_π]
    simp only [Pi.map_apply, Types.productIso_hom_comp_eval_apply]

    let _ : X.val.obj (⟨∐ S⟩) ⟶ X.val.obj (∏ᶜ fun i ↦ ⟨S i⟩) := (X.val.map (opCoproductIsoProduct S).hom)

    let _ : X.val.obj (⟨∐ S⟩) ⟶ X.val.obj ⟨S i⟩ :=
      (X.val.map (opCoproductIsoProduct S).hom) ≫ piComparison X.val (fun i ↦ ⟨S i⟩) ≫ Pi.π (fun i ↦ X.val.obj ⟨S i⟩) i

    change
      _ =
      (LightCondensed.yoneda (S i) X).symm (
        (
          (X.val.map (opCoproductIsoProduct S).hom)
            ≫ piComparison X.val (fun i ↦ ⟨S i⟩)
            ≫ Pi.π (fun i ↦ X.val.obj ⟨S i⟩) i
        )
        (LightCondensed.yoneda (∐ S) X f)
      )
    rw [
        piComparison_comp_π,
        ←X.val.map_comp,
        opCoproductIsoProduct_hom_comp_π
    ]
    rw [
        yoneda_obj_map,
        ←unop_comp_assoc,
        opCoproductIsoProduct_hom_comp_π,
        Quiver.Hom.unop_op,
        ι_comp_sigmaComparison_assoc,
        ←yoneda_symm_naturality
    ]
    change _ = (lightProfiniteToLightCondSet.map (Sigma.ι S i) ≫
    (((LightCondensed.yoneda (∐ S) X).symm ∘ (LightCondensed.yoneda (∐ S) X)) f))
    rw [Equiv.symm_comp_self, id_eq]

  -- Now the approach is to write `(coyoneda.map (sigmaComparison _ _).op).app X` as
  -- `piComparison X.val _` pre- and post-composed with isos given by the coyoneda lemma.
  -- The issue is that the homs in `LightCondSet` a priori live in one universe higher than the
  -- S-valued points of `X` (but they are small). There is some API in a file called
  -- `LightCondensed/Yoneda.lean` in the condensed repo that might be helpful.
  rw [this]
  exact map_bij

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{u} where
  preserves n :=
    { preservesColimit {S} := by
        let i : S ≅ Discrete.functor (fun i ↦ S.obj ⟨i⟩) := Discrete.natIso (fun _ ↦ Iso.refl _)
        exact preservesColimit_of_iso_diagram lightProfiniteToLightCondSet i.symm
    }
