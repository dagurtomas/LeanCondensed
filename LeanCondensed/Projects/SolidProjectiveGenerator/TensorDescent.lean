module

public import LeanCondensed.Projects.SolidProjectiveGenerator.BoundedSequences
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The module scalar action of integers on a `ModuleCat ℤ` object commutes with itself. -/
theorem intModuleCatModuleSMulComm (M : ModuleCat ℤ) :
    @SMulCommClass ℤ ℤ (↑M) M.isModule.toDistribMulAction.toSMul
      M.isModule.toDistribMulAction.toSMul := by
  let d : DistribMulAction ℤ (↑M) := M.isModule.toDistribMulAction
  refine @SMulCommClass.mk ℤ ℤ (↑M) d.toSMul d.toSMul ?_
  intro a b x
  show d.smul a (d.smul b x) = d.smul b (d.smul a x)
  calc
    d.smul a (d.smul b x) = d.smul (a * b) x := (d.mul_smul a b x).symm
    _ = d.smul (b * a) x := by rw [mul_comm]
    _ = d.smul b (d.smul a x) := d.mul_smul b a x

abbrev freeTensorSectionHom (X : LightProfinite.{0}) (S : LightProfiniteᵒᵖ)
    (f : X.toCondensed.obj.obj S) : S.unop ⟶ X := f

@[simp]
lemma freeTensorSectionHom_map (X : LightProfinite.{0}) {S T : LightProfiniteᵒᵖ}
    (φ : S ⟶ T) (f : X.toCondensed.obj.obj S) :
    freeTensorSectionHom X T (X.toCondensed.obj.map φ f) = φ.unop ≫ freeTensorSectionHom X S f := rfl

noncomputable def freeTensorPresheafDescLin (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X) (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m)) :
    (X.toCondensed.obj ⋙ ModuleCat.free ℤ) ⊗ B.obj ⟶ C.obj where
  app S := by
    letI hC : @SMulCommClass ℤ ℤ (↑(C.obj.obj S)) (C.obj.obj S).isModule.toDistribMulAction.toSMul (C.obj.obj S).isModule.toDistribMulAction.toSMul := intModuleCatModuleSMulComm (C.obj.obj S)
    letI : Module ℤ (B.obj.obj S →ₗ[ℤ] C.obj.obj S) :=
      @LinearMap.module ℤ ℤ ℤ (B.obj.obj S) (C.obj.obj S) _ _ _ _ _ _ (RingHom.id ℤ) _ _ hC
    let L : ((X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj S) →ₗ[ℤ]
        (B.obj.obj S →ₗ[ℤ] C.obj.obj S) :=
      Finsupp.lift (B.obj.obj S →ₗ[ℤ] C.obj.obj S) ℤ (X.toCondensed.obj.obj S)
        (fun f => b S.unop (freeTensorSectionHom X S f))
    exact ModuleCat.ofHom (TensorProduct.lift L)
  naturality := by
    intro S T φ
    letI hCS : @SMulCommClass ℤ ℤ (↑(C.obj.obj S)) (C.obj.obj S).isModule.toDistribMulAction.toSMul (C.obj.obj S).isModule.toDistribMulAction.toSMul := intModuleCatModuleSMulComm (C.obj.obj S)
    letI hCT : @SMulCommClass ℤ ℤ (↑(C.obj.obj T)) (C.obj.obj T).isModule.toDistribMulAction.toSMul (C.obj.obj T).isModule.toDistribMulAction.toSMul := intModuleCatModuleSMulComm (C.obj.obj T)
    letI : Module ℤ (B.obj.obj S →ₗ[ℤ] C.obj.obj S) :=
      @LinearMap.module ℤ ℤ ℤ (B.obj.obj S) (C.obj.obj S) _ _ _ _ _ _ (RingHom.id ℤ) _ _ hCS
    letI : Module ℤ (B.obj.obj T →ₗ[ℤ] C.obj.obj T) :=
      @LinearMap.module ℤ ℤ ℤ (B.obj.obj T) (C.obj.obj T) _ _ _ _ _ _ (RingHom.id ℤ) _ _ hCT
    letI : Module ℤ (B.obj.obj S →ₗ[ℤ] C.obj.obj T) :=
      @LinearMap.module ℤ ℤ ℤ (B.obj.obj S) (C.obj.obj T) _ _ _ _ _ _ (RingHom.id ℤ) _ _ hCT
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a m
    change (TensorProduct.lift
        ((Finsupp.lift (B.obj.obj T →ₗ[ℤ] C.obj.obj T) ℤ (X.toCondensed.obj.obj T)) fun f =>
          b T.unop (freeTensorSectionHom X T f)))
      ((((ModuleCat.free ℤ).map (X.toCondensed.obj.map φ) ⊗ₘ B.obj.map φ) (a ⊗ₜ[ℤ] m))) =
    (C.obj.map φ)
      ((((Finsupp.lift (B.obj.obj S →ₗ[ℤ] C.obj.obj S) ℤ (X.toCondensed.obj.obj S)) fun f =>
          b S.unop (freeTensorSectionHom X S f)) a) m)
    dsimp [ModuleCat.free] at *
    let LT : (X.toCondensed.obj.obj T →₀ ℤ) →ₗ[ℤ]
        (B.obj.obj T →ₗ[ℤ] C.obj.obj T) :=
      (Finsupp.lift (B.obj.obj T →ₗ[ℤ] C.obj.obj T) ℤ (X.toCondensed.obj.obj T)) fun f =>
        b T.unop (freeTensorSectionHom X T f)
    let LS : (X.toCondensed.obj.obj S →₀ ℤ) →ₗ[ℤ]
        (B.obj.obj S →ₗ[ℤ] C.obj.obj S) :=
      (Finsupp.lift (B.obj.obj S →ₗ[ℤ] C.obj.obj S) ℤ (X.toCondensed.obj.obj S)) fun f =>
        b S.unop (freeTensorSectionHom X S f)
    let freeMap : (X.toCondensed.obj.obj S →₀ ℤ) →ₗ[ℤ]
        (X.toCondensed.obj.obj T →₀ ℤ) :=
      Finsupp.lmapDomain ℤ ℤ (X.toCondensed.obj.map φ)
    let preB : (B.obj.obj T →ₗ[ℤ] C.obj.obj T) →ₗ[ℤ]
        (B.obj.obj S →ₗ[ℤ] C.obj.obj T) :=
      LinearMap.lcomp ℤ (C.obj.obj T) (ModuleCat.Hom.hom (B.obj.map φ))
    let postC : (B.obj.obj S →ₗ[ℤ] C.obj.obj S) →ₗ[ℤ]
        (B.obj.obj S →ₗ[ℤ] C.obj.obj T) := {
      toFun := fun l => (ModuleCat.Hom.hom (C.obj.map φ)).comp l
      map_add' := by
        intro l₁ l₂
        ext m
        simp
      map_smul' := by
        intro r l
        ext m
        simp }
    change ((preB.comp (LT.comp freeMap)) a) m = ((postC.comp LS) a) m
    have hlin : preB.comp (LT.comp freeMap) = postC.comp LS := by
      apply Finsupp.lhom_ext'
      intro f
      apply LinearMap.ext
      intro r
      apply LinearMap.ext
      intro m
      dsimp [preB, postC, LT, LS, freeMap]
      rw [Finsupp.mapDomain_single]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
      · rw [freeTensorSectionHom_map]
        rw [show φ = φ.unop.op by rfl]
        rw [Quiver.Hom.unop_op]
        rw [LinearMap.smul_apply]
        rw [LinearMap.smul_apply]
        rw [(ModuleCat.Hom.hom (C.obj.map φ.unop.op)).map_smul]
        rw [hnat φ.unop (freeTensorSectionHom X S f) m]
      · apply LinearMap.ext
        intro m
        rw [LinearMap.smul_apply]
        let mod : Module ℤ (C.obj.obj S) := (C.obj.obj S).isModule
        change mod.toDistribMulAction.smul 0 ((b S.unop (freeTensorSectionHom X S f)) m) = 0
        exact mod.zero_smul ((b S.unop (freeTensorSectionHom X S f)) m)
      · apply LinearMap.ext
        intro m
        rw [LinearMap.smul_apply]
        let mod : Module ℤ (C.obj.obj T) := (C.obj.obj T).isModule
        change mod.toDistribMulAction.smul 0 ((b T.unop (freeTensorSectionHom X T (X.toCondensed.obj.map φ f))) m) = 0
        exact mod.zero_smul ((b T.unop (freeTensorSectionHom X T (X.toCondensed.obj.map φ f))) m)
    rw [hlin]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
noncomputable def freeTensorDescLin (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X) (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m)) :
    ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  letI : L.Monoidal := inferInstanceAs ((presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)).Monoidal)
  let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let α : F ⊗ G ⟶ C.obj := freeTensorPresheafDescLin X B C b hnat
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let cC : L.obj C.obj ⟶ C :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app C
  haveI : IsIso cB := by
    dsimp [cB, G, L]
    exact isIso_sheafificationAdjunction_counit B
  haveI : IsIso cC := by
    dsimp [cC, L]
    exact isIso_sheafificationAdjunction_counit C
  let cBinv : B ⟶ L.obj G := inv cB
  change L.obj F ⊗ B ⟶ C
  exact (L.obj F ◁ cBinv) ≫
    (Functor.Monoidal.μIso L F G).hom ≫ L.map α ≫ cC

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- After replacing the sheafified right tensor factor by the original sheaf, the descended
free-tensor map is the sheafification of its defining presheaf-level map. -/
lemma freeTensorDescLin_fac (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m)) :
    let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
    let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
    let α : F ⊗ G ⟶ C.obj := freeTensorPresheafDescLin X B C b hnat
    let cB : L.obj G ⟶ B :=
      (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
    let cC : L.obj C.obj ⟶ C :=
      (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app C
    (L.obj F ◁ cB) ≫ freeTensorDescLin X B C b hnat =
      (Functor.Monoidal.μIso L F G).hom ≫ L.map α ≫ cC := by
  intro L F G α cB cC
  haveI : IsIso cB := by
    dsimp [cB, G, L]
    exact isIso_sheafificationAdjunction_counit B
  dsimp [freeTensorDescLin]
  simp [cB, cC, L, F, G, α]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification part of `freeTensorDescLin` has the expected presheaf-level
factorization. -/
lemma freeTensorDescLin_sheafify_fac (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m)) :
    let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
    let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
    let α : F ⊗ G ⟶ C.obj := freeTensorPresheafDescLin X B C b hnat
    let cC : L.obj C.obj ⟶ C :=
      (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app C
    CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
      ((L.map α ≫ cC).hom) = α := by
  intro L F G α cC
  change CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
      CategoryTheory.sheafifyMap (coherentTopology LightProfinite) α ≫ cC.hom = α
  rw [← CategoryTheory.toSheafify_naturality_assoc]
  dsimp [cC]
  rw [CategoryTheory.sheafificationAdjunction_counit_app_val]
  rw [CategoryTheory.toSheafify_sheafifyLift]
  simp

/-- Maps out of a free light condensed abelian group are the corresponding point values. -/
noncomputable def freeHomEquivPoints (T : LightProfinite) (A : LightCondAb) :
    ((free ℤ).obj T.toCondensed ⟶ A) ≃ A.obj.obj ⟨T⟩ :=
  ((freeForgetAdjunction ℤ).homEquiv T.toCondensed A).trans
    (coherentTopology LightProfinite).yonedaEquiv

lemma freeHomEquivPoints_map {T T' : LightProfinite} (φ : T' ⟶ T)
    (A : LightCondAb) (f : (free ℤ).obj T.toCondensed ⟶ A) :
    freeHomEquivPoints T' A (((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫ f) =
      A.obj.map φ.op (freeHomEquivPoints T A f) := by
  dsimp [freeHomEquivPoints]
  erw [Adjunction.homEquiv_naturality_left]
  exact (GrothendieckTopology.yonedaEquiv_naturality (coherentTopology LightProfinite)
    (((freeForgetAdjunction ℤ).homEquiv T.toCondensed A) f) φ).symm

lemma freeHomEquivPoints_symm_map {T T' : LightProfinite} (φ : T' ⟶ T)
    (A : LightCondAb) (x : A.obj.obj ⟨T⟩) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫
      (freeHomEquivPoints T A).symm x =
      (freeHomEquivPoints T' A).symm (A.obj.map φ.op x) := by
  apply (freeHomEquivPoints T' A).injective
  rw [freeHomEquivPoints_map]
  simp

/-- The point-value description of maps out of a free object is natural in the target. -/
lemma freeHomEquivPoints_comp (T : LightProfinite) {A B : LightCondAb}
    (f : (free ℤ).obj T.toCondensed ⟶ A) (φ : A ⟶ B) :
    freeHomEquivPoints T B (f ≫ φ) =
      φ.hom.app ⟨T⟩ (freeHomEquivPoints T A f) := by
  dsimp [freeHomEquivPoints]
  erw [Adjunction.homEquiv_naturality_right]
  erw [GrothendieckTopology.yonedaEquiv_comp]

@[simp]
lemma freeHomEquivPoints_zero (T : LightProfinite) (A : LightCondAb) :
    freeHomEquivPoints T A (0 : (free ℤ).obj T.toCondensed ⟶ A) = 0 := by
  have h := freeHomEquivPoints_comp T (𝟙 ((free ℤ).obj T.toCondensed))
    (0 : (free ℤ).obj T.toCondensed ⟶ A)
  simpa using h

/-- The point-value description of maps out of a free object preserves subtraction. -/
lemma freeHomEquivPoints_sub (T : LightProfinite) (A : LightCondAb)
    (f g : (free ℤ).obj T.toCondensed ⟶ A) :
    freeHomEquivPoints T A (f - g) =
      freeHomEquivPoints T A f - freeHomEquivPoints T A g := by
  change (show A.obj.obj ⟨T⟩ from (coherentTopology LightProfinite).yonedaEquiv
      (((freeForgetAdjunction ℤ).homEquiv T.toCondensed A) (f - g))) =
    (show A.obj.obj ⟨T⟩ from (coherentTopology LightProfinite).yonedaEquiv
      (((freeForgetAdjunction ℤ).homEquiv T.toCondensed A) f)) -
    (show A.obj.obj ⟨T⟩ from (coherentTopology LightProfinite).yonedaEquiv
      (((freeForgetAdjunction ℤ).homEquiv T.toCondensed A) g))
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  let u := (((freeForgetAdjunction ℤ).unit.app T.toCondensed).hom.app ⟨T⟩ (𝟙 T))
  change (show A.obj.obj ⟨T⟩ from ((forget ℤ).map (f - g)).hom.app ⟨T⟩ u) =
    (show A.obj.obj ⟨T⟩ from ((forget ℤ).map f).hom.app ⟨T⟩ u) -
    (show A.obj.obj ⟨T⟩ from ((forget ℤ).map g).hom.app ⟨T⟩ u)
  change (f - g).hom.app ⟨T⟩ u = f.hom.app ⟨T⟩ u - g.hom.app ⟨T⟩ u
  rfl

/-- The free/topological-free comparison sends the free map induced by a continuous map to the
corresponding Dirac family. -/
lemma freeMap_topologicalFree_apply {S T : LightProfinite} (f : S ⟶ T) (s : S) :
    (show C(↑S.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩
        (freeHomEquivPoints S ((free ℤ).obj T.toCondensed)
          ((free ℤ).map (lightProfiniteToLightCondSet.map f)))) s =
      Finsupp.single (f s) (1 : ℤ) := by
  have hcomp := (freeHomEquivPoints_comp S
    ((free ℤ).map (lightProfiniteToLightCondSet.map f))
    (LightCondAb.freeToTopologicalFree T)).symm
  have hsec : (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩
        (freeHomEquivPoints S ((free ℤ).obj T.toCondensed)
          ((free ℤ).map (lightProfiniteToLightCondSet.map f))) =
      freeHomEquivPoints S (LightCondAb.topologicalFreeCondensed T)
        (((free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫
          LightCondAb.freeToTopologicalFree T) := by
    simpa using hcomp
  rw [hsec]
  change (show C(↑S.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      freeHomEquivPoints S (LightCondAb.topologicalFreeCondensed T)
        (((free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫
          LightCondAb.freeToTopologicalFree T)) s = _
  rw [LightCondAb.freeToTopologicalFree_naturality]
  have hcomp2 := (freeHomEquivPoints_comp S (LightCondAb.freeToTopologicalFree S)
    (LightCondAb.topologicalFreeCondensedMap f)).symm
  have hsec2 : freeHomEquivPoints S (LightCondAb.topologicalFreeCondensed T)
      (LightCondAb.freeToTopologicalFree S ≫ LightCondAb.topologicalFreeCondensedMap f) =
      (LightCondAb.topologicalFreeCondensedMap f).hom.app ⟨S⟩
        (freeHomEquivPoints S (LightCondAb.topologicalFreeCondensed S)
          (LightCondAb.freeToTopologicalFree S)) := by
    simpa using hcomp2.symm
  rw [hsec2]
  have hfree : freeHomEquivPoints S (LightCondAb.topologicalFreeCondensed S)
      (LightCondAb.freeToTopologicalFree S) =
      (coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection S) := by
    simp [LightCondAb.freeToTopologicalFree, freeHomEquivPoints]
    rfl
  rw [hfree]
  change (LightCondAb.topologicalFreeMap f).hom
      ((show C(↑S.toTop, ↑(LightCondAb.topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection S)) s) = _
  rw [LightCondAb.topologicalFreeDiracSection_yoneda_apply]
  rw [LightCondAb.topologicalFreeMap_single]

/-- The identity endomorphism corresponds to the topological Dirac family. -/
lemma freeToTopologicalFree_id_apply (T : LightProfinite) (t : T) :
    (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed) (𝟙 _))) t =
      Finsupp.single t (1 : ℤ) := by
  have hcomp := (freeHomEquivPoints_comp T (𝟙 ((free ℤ).obj T.toCondensed))
    (LightCondAb.freeToTopologicalFree T)).symm
  have hsec : (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed) (𝟙 _)) =
      freeHomEquivPoints T (LightCondAb.topologicalFreeCondensed T)
        (LightCondAb.freeToTopologicalFree T) := by
    simpa using hcomp
  rw [hsec]
  have hfree : freeHomEquivPoints T (LightCondAb.topologicalFreeCondensed T)
      (LightCondAb.freeToTopologicalFree T) =
      (coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection T) := by
    simp [LightCondAb.freeToTopologicalFree, freeHomEquivPoints]
    rfl
  rw [hfree]
  exact LightCondAb.topologicalFreeDiracSection_yoneda_apply T t

/-- The free light condensed abelian group on the point is the tensor unit. -/
noncomputable def freePointIsoUnit :
    (LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ≅ 𝟙_ LightCondAb :=
  (LightCondensed.free ℤ).mapIso (Functor.Monoidal.εIso lightProfiniteToLightCondSet).symm ≪≫
    (Functor.Monoidal.εIso (LightCondensed.free ℤ)).symm

/-- The free light condensed abelian group on the point is projective: local lifts over a cover of
`*` can be pulled back along any chosen point of the cover. -/
instance freePoint_projective :
    Projective ((LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) where
  factors {A B} f e he := by
    letI : Epi e := he
    let pt : LightProfinite := LightProfinite.of PUnit.{1}
    obtain ⟨T, π, g, hπ, hg⟩ :=
      LightCondMod.factorsThru_lightProfinite_epi_of_epi ℤ e (S := pt) f
    have hπsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp hπ
    obtain ⟨t, ht⟩ := hπsurj PUnit.unit
    let σ : pt ⟶ T := ConcreteCategory.ofHom ⟨fun _ => t, continuous_const⟩
    have hσπ : σ ≫ π = 𝟙 pt := by
      ext x
    refine ⟨(LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map σ) ≫ g, ?_⟩
    simp only [Category.assoc]
    rw [← hg]
    change (LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map σ) ≫
        ((LightCondensed.free ℤ).map (lightProfiniteToLightCondSet.map π) ≫ f) = f
    rw [← Category.assoc]
    simp [← Functor.map_comp, hσπ]

/-- The tensor unit of light condensed abelian groups is projective. -/
instance tensorUnit_projective : Projective (𝟙_ LightCondAb) :=
  Projective.of_iso freePointIsoUnit freePoint_projective

/-- The object `P ℤ` is projective in light condensed abelian groups. -/
instance projective_P : Projective (P ℤ) := by
  haveI : Projective (𝟙_ LightCondAb) := tensorUnit_projective
  exact CategoryTheory.projective_of_internallyProjective_of_projective_unit (P ℤ)

/-- Solidification preserves projective objects because its right adjoint, the inclusion of solid
objects, preserves epimorphisms. -/
instance solidification_preservesProjectiveObjects :
    solidification.PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    solidificationAdjunction

/-- The solidification of `P ℤ` is projective in `Solid`. -/
instance projective_solidP : Projective solidP := by
  dsimp [solidP]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary currying intertwines external precomposition with internal precomposition. -/
lemma curry'_pre_app {X Y Z : LightCondAb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MonoidalClosed.curry' (f ≫ g) =
      MonoidalClosed.curry' g ≫ (MonoidalClosed.pre f).app Z := by
  dsimp [MonoidalClosed.curry']
  rw [MonoidalClosed.curry_pre_app]
  congr 1
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The defining map `1 - shift : P ℤ ⟶ P ℤ` is local for the solidification localization. -/
lemma oneMinusShift_mem_isLocal : isSolid.isLocal (oneMinusShift ℤ) := by
  intro Z hZ
  dsimp [isSolid] at hZ
  let φ := ((MonoidalClosed.pre (oneMinusShift ℤ)).app Z)
  haveI : IsIso φ := hZ
  have hcompat : ∀ g : P ℤ ⟶ Z,
      MonoidalClosed.curry' ((oneMinusShift ℤ) ≫ g) = MonoidalClosed.curry' g ≫ φ := by
    intro g
    exact curry'_pre_app (oneMinusShift ℤ) g
  constructor
  · intro g₁ g₂ h
    apply MonoidalClosed.curry'_injective
    apply (cancel_mono φ).1
    rw [← hcompat, ← hcompat]
    exact congrArg MonoidalClosed.curry' h
  · intro g
    let a : 𝟙_ LightCondAb ⟶ (ihom (P ℤ)).obj Z := MonoidalClosed.curry' g ≫ inv φ
    refine ⟨MonoidalClosed.uncurry' a, ?_⟩
    apply MonoidalClosed.curry'_injective
    rw [hcompat]
    dsimp [a, φ]
    simp

/-- Tensoring `1 - shift` on the right is inverted by solidification. -/
lemma solidification_map_oneMinusShift_tensor_isIso (M : LightCondAb) :
    IsIso (solidification.map ((oneMinusShift ℤ) ▷ M)) := by
  apply Localization.inverts solidification isSolid.isLocal
  exact isSolid.isLocal.whiskerRight_mem (oneMinusShift ℤ) oneMinusShift_mem_isLocal M

/-- Obligation: the solidification of `P ℤ` is the countable product of copies of `ℤ`.  This is the
heart-level form of the paper's bounded-sequence and derived-solidification calculation. -/
noncomputable def solidPIsoProduct : solidP ≅ productInt := by
  sorry

/-- Homs from solidified free representables are their values on the representing test object. -/
noncomputable def solidifiedFreeHomEquiv
    (T : LightProfinite) (A : Solid) :
    (solidification.obj ((free ℤ).obj T.toCondensed) ⟶ A) ≃ A.1.obj.obj ⟨T⟩ :=
  (solidificationAdjunction.homEquiv ((free ℤ).obj T.toCondensed) A).trans
    (((LightCondensed.freeForgetAdjunction ℤ).homEquiv T.toCondensed (isSolid.ι.obj A)).trans
      (coherentTopology LightProfinite).yonedaEquiv)

lemma solidifiedFreeHomEquiv_comp
    (T : LightProfinite) {A B : Solid}
    (k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ A)
    (f : A ⟶ B) :
    solidifiedFreeHomEquiv T B (k ≫ f) =
      ((isSolid.ι.map f).hom.app ⟨T⟩)
        (solidifiedFreeHomEquiv T A k) := by
  dsimp [solidifiedFreeHomEquiv]
  erw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  erw [GrothendieckTopology.yonedaEquiv_comp]

/-- Solidified free representables jointly separate solid objects. -/
lemma solidifiedFree_hom_ext
    {X Y : Solid} (f g : X ⟶ Y)
    (h : ∀ (T : LightProfinite)
      (k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ X),
      k ≫ f = k ≫ g) :
    f = g := by
  apply isSolid.ι.map_injective
  ext S x
  rcases S with ⟨T⟩
  let k : solidification.obj ((free ℤ).obj T.toCondensed) ⟶ X :=
    (solidifiedFreeHomEquiv T X).symm x
  have hk := h T k
  have hpoint := congrArg (solidifiedFreeHomEquiv T Y) hk
  change solidifiedFreeHomEquiv T Y (k ≫ f) = solidifiedFreeHomEquiv T Y (k ≫ g) at hpoint
  rw [solidifiedFreeHomEquiv_comp, solidifiedFreeHomEquiv_comp] at hpoint
  have hx : (solidifiedFreeHomEquiv T X) k = x := by
    dsimp [k]
    rw [Equiv.apply_symm_apply]
  rw [hx] at hpoint
  exact hpoint

end ProjectiveGeneratorProof
end Solid
end LightCondensed
