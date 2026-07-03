module

public import LeanCondensed.Projects.SolidProjectiveGenerator.TensorDescent
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- Enlarge a light profinite set by adding the convergent-sequence object.  This is infinite and
contains the original object as a coproduct summand. -/
noncomputable abbrev infiniteEnvelope (S : LightProfinite) : LightProfinite :=
  S ⨿ (ℕ∪{∞} : LightProfinite)

instance infiniteEnvelope_infinite (S : LightProfinite) : Infinite (infiniteEnvelope S) := by
  let f : (ℕ∪{∞} : LightProfinite) → ↑(infiniteEnvelope S).toTop := fun x =>
    (ConcreteCategory.hom (coprod.inr : (ℕ∪{∞} : LightProfinite) ⟶ infiniteEnvelope S)) x
  have hf : Function.Injective f := by
    dsimp [f, infiniteEnvelope]
    exact (CompHausLike.mono_iff_injective
      (coprod.inr : (ℕ∪{∞} : LightProfinite) ⟶ S ⨿ ℕ∪{∞})).mp inferInstance
  exact Infinite.of_injective (α := ↑(infiniteEnvelope S).toTop)
    (β := (ℕ∪{∞} : LightProfinite)) f hf

/-- The free object on `S` is a retract of the free object on its infinite envelope. -/
noncomputable def freeRetractIntoInfinite (S : LightProfinite) :
    Retract
      ((free ℤ).obj S.toCondensed)
      ((free ℤ).obj (infiniteEnvelope S).toCondensed) := by
  simpa [infiniteEnvelope] using
    CategoryTheory.functor_obj_retract_coprod
      (lightProfiniteToLightCondSet ⋙ free ℤ) S (ℕ∪{∞} : LightProfinite)

/-- The free-module map induced by the `n`th finite projection of a light profinite set. -/
noncomputable def freeProj (T : LightProfinite) (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj (T.component n).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (T.proj n)

/-- The constant map from the point to a light profinite space selecting `x`. -/
noncomputable def pointMap (X : LightProfinite) (x : X) :
    LightProfinite.of PUnit.{1} ⟶ X :=
  ConcreteCategory.ofHom ⟨fun _ => x, continuous_const⟩

@[simp]
lemma pointMap_apply (X : LightProfinite) (x : X) (u : LightProfinite.of PUnit.{1}) :
    pointMap X x u = x := rfl

/-- The free-module map induced by a point of a light profinite space. -/
noncomputable def freePointMap (T : LightProfinite) (t : T) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t)

@[simp]
lemma pointMap_comp (T S : LightProfinite) (f : T ⟶ S) (t : T) :
    pointMap T t ≫ f = pointMap S (f t) := by
  ext u
  rfl

lemma freePointMap_comp (T S : LightProfinite) (f : T ⟶ S) (t : T) :
    freePointMap T t ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map f =
      freePointMap S (f t) := by
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t) ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map f =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap S (f t))
  rw [← Functor.map_comp]
  rw [pointMap_comp]

lemma freePointMap_comp_freeProj (T : LightProfinite) (k : ℕ) (t : T) :
    freePointMap T t ≫ freeProj T k = freePointMap (T.component k) (T.proj k t) := by
  exact freePointMap_comp T (T.component k) (T.proj k) t

/-- The unique map from `T` to the point. -/
noncomputable def toPointMap (T : LightProfinite) : T ⟶ LightProfinite.of PUnit.{1} :=
  ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

@[simp]
lemma pointMap_point_eq_id : pointMap (LightProfinite.of PUnit.{1}) PUnit.unit = 𝟙 _ := by
  ext x

/-- A chosen point of `T`, followed by the map to the point, gives the identity on the free point. -/
lemma freePointMap_comp_toPointMap (T : LightProfinite) (t : T) :
    freePointMap T t ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) =
      𝟙 ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) := by
  rw [freePointMap_comp]
  dsimp [toPointMap]
  change freePointMap (LightProfinite.of PUnit.{1}) PUnit.unit = 𝟙 _
  dsimp [freePointMap]
  rw [pointMap_point_eq_id]
  simp

/-- The sheaf morphism obtained by evaluating a sectionwise family at a fixed point of the
left free variable. -/
noncomputable def freeTensorFamilyMap (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m))
    (x : LightProfinite.of PUnit.{1} ⟶ X) : B ⟶ C where
  hom := {
    app S := ModuleCat.ofHom (b S.unop (toPointMap S.unop ≫ x))
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext m
      change b T.unop (toPointMap T.unop ≫ x) (B.obj.map φ.unop.op m) =
        C.obj.map φ.unop.op (b S.unop (toPointMap S.unop ≫ x) m)
      have hto : φ.unop ≫ toPointMap S.unop = toPointMap T.unop := by
        ext t
      rw [← hto]
      simpa [Category.assoc] using (hnat φ.unop (toPointMap S.unop ≫ x) m).symm }

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The presheaf-level unit vector determined by a point of the free variable. -/
noncomputable def freeTensorPointUnit (X : LightProfinite.{0})
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    𝟙_ (LightProfiniteᵒᵖ ⥤ ModuleCat ℤ) ⟶ X.toCondensed.obj ⋙ ModuleCat.free ℤ where
  app S := ModuleCat.ofHom {
    toFun := fun r => Finsupp.single (toPointMap S.unop ≫ x) r
    map_add' := by
      intro a b
      ext f
      by_cases h : f = toPointMap S.unop ≫ x <;> simp [h]
    map_smul' := by
      intro a r
      ext f
      by_cases h : f = toPointMap S.unop ≫ x <;> simp [h] }
  naturality := by
    intro S T φ
    rw [show φ = φ.unop.op by rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Finsupp.single (toPointMap T.unop ≫ x) r =
      Finsupp.lmapDomain ℤ ℤ (X.toCondensed.obj.map φ.unop.op)
        (Finsupp.single (toPointMap S.unop ≫ x) r)
    ext f
    rw [Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_single]
    have hto : φ.unop ≫ toPointMap S.unop = toPointMap T.unop := by ext t
    rw [← hto]
    rfl

/-- The point-unit map is the presheaf-level form of the free point/unit isomorphism. -/
lemma freeTensorPointUnit_eq (X : LightProfinite.{0})
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    freeTensorPointUnit X x =
      Functor.LaxMonoidal.ε
        ((Functor.whiskeringRight LightProfiniteᵒᵖ (Type 0) (ModuleCat ℤ)).obj (ModuleCat.free ℤ)) ≫
      𝟙 (𝟙_ (LightProfiniteᵒᵖ ⥤ Type) ⋙ ModuleCat.free ℤ) ≫
      Functor.whiskerRight (Functor.LaxMonoidal.ε lightProfiniteToLightCondSet).hom
        (ModuleCat.free ℤ) ≫
      Functor.whiskerRight (lightProfiniteToLightCondSet.map x).hom (ModuleCat.free ℤ) := by
  ext S
  change Finsupp.single (toPointMap S.unop ≫ x) (1 : ℤ) =
    (ConcreteCategory.hom ((ModuleCat.free ℤ).map ((lightProfiniteToLightCondSet.map x).hom.app S)))
      ((ConcreteCategory.hom ((ModuleCat.free ℤ).map
        ((Functor.LaxMonoidal.ε lightProfiniteToLightCondSet).hom.app S)))
        ((ConcreteCategory.hom (Functor.LaxMonoidal.ε (ModuleCat.free ℤ))) 1))
  rw [ModuleCat.free_ε_one]
  rw [ModuleCat.free_map_apply]
  rw [ModuleCat.free_map_apply]
  rfl

/-- Sheafifying the point-unit map gives the chosen map out of the tensor unit. -/
lemma freeTensorPointUnit_sheafify (X : LightProfinite.{0})
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    Functor.LaxMonoidal.ε L ≫ L.map (freeTensorPointUnit X x) =
      freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x) := by
  intro L
  rw [freeTensorPointUnit_eq]
  dsimp [freePointIsoUnit, LightCondensed.free, CategoryTheory.Sheaf.composeAndSheafify]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.Monoidal.εIso_hom,
    Functor.LaxMonoidal.comp_ε, ObjectProperty.ι_obj,
    CartesianMonoidalCategory.fullSubcategory_tensorUnit_obj, ObjectProperty.ι_ε,
    Functor.comp_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_id',
    Category.assoc, Functor.mapIso_hom, ObjectProperty.ι_map]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]

/-- The presheaf-level pure tensor map determined by a point of the left free variable. -/
noncomputable def freeTensorPresheafPoint (X : LightProfinite.{0}) (B : LightCondAb)
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    B.obj ⟶ (X.toCondensed.obj ⋙ ModuleCat.free ℤ) ⊗ B.obj where
  app S := ModuleCat.ofHom
    ((TensorProduct.mk ℤ ((X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj S) (B.obj.obj S))
      (Finsupp.single (toPointMap S.unop ≫ x) (1 : ℤ)))
  naturality := by
    intro S T φ
    rw [show φ = φ.unop.op by rfl]
    ext m
    change (Finsupp.single (toPointMap T.unop ≫ x) (1 : ℤ)) ⊗ₜ[ℤ]
        (B.obj.map φ.unop.op m) =
      (Finsupp.lmapDomain ℤ ℤ (X.toCondensed.obj.map φ.unop.op)
        (Finsupp.single (toPointMap S.unop ≫ x) (1 : ℤ))) ⊗ₜ[ℤ]
          (B.obj.map φ.unop.op m)
    rw [Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_single]
    congr 1

/-- The pure tensor map is obtained from the point-unit map and the left unitor. -/
lemma freeTensorPresheafPoint_eq (X : LightProfinite.{0}) (B : LightCondAb)
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    freeTensorPresheafPoint X B x =
      (λ_ B.obj).inv ≫ (freeTensorPointUnit X x ▷ B.obj) := by
  ext S m
  rfl

/-- The point slice is compatible with the monoidal structure on sheafification. -/
lemma freeTensorPresheafPoint_sheafify_comp (X : LightProfinite.{0}) (B : LightCondAb)
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
    let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
    CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
      (((λ_ (L.obj G)).inv ≫
        (freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)) ▷ L.obj G ≫
        (Functor.Monoidal.μIso L F G).hom).hom) =
      freeTensorPresheafPoint X B x ≫
        CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) := by
  intro L F G
  have hunit := freeTensorPointUnit_sheafify X x
  dsimp only at hunit
  rw [← hunit]
  have hsheaf :
      (λ_ (L.obj G)).inv ≫
          (Functor.LaxMonoidal.ε L ≫ L.map (freeTensorPointUnit X x)) ▷ L.obj G ≫
          (Functor.Monoidal.μIso L F G).hom =
        L.map (freeTensorPresheafPoint X B x) := by
    rw [freeTensorPresheafPoint_eq]
    simp only [comp_whiskerRight, Category.assoc, Functor.Monoidal.μIso_hom]
    slice_lhs 3 4 => rw [Functor.LaxMonoidal.μ_natural_left L (freeTensorPointUnit X x) G]
    slice_lhs 1 3 => rw [Functor.LaxMonoidal.left_unitality_inv L G]
    rw [← Functor.map_comp]
  rw [hsheaf]
  rw [← CategoryTheory.toSheafify_naturality]

/-- Evaluating the defining presheaf-level tensor map at a point gives the corresponding
sectionwise family map. -/
lemma freeTensorPresheafPoint_desc (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m))
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    freeTensorPresheafPoint X B x ≫ freeTensorPresheafDescLin X B C b hnat =
      (freeTensorFamilyMap X B C b hnat x).hom := by
  ext S m
  letI hC : @SMulCommClass ℤ ℤ (↑(C.obj.obj S))
      (C.obj.obj S).isModule.toDistribMulAction.toSMul
      (C.obj.obj S).isModule.toDistribMulAction.toSMul :=
    intModuleCatModuleSMulComm (C.obj.obj S)
  letI : Module ℤ (B.obj.obj S →ₗ[ℤ] C.obj.obj S) :=
    @LinearMap.module ℤ ℤ ℤ (B.obj.obj S) (C.obj.obj S) _ _ _ _ _ _
      (RingHom.id ℤ) _ _ hC
  change (TensorProduct.lift
      ((Finsupp.lift (B.obj.obj S →ₗ[ℤ] C.obj.obj S) ℤ (X.toCondensed.obj.obj S)) fun f =>
        b S.unop (freeTensorSectionHom X S f)))
      ((Finsupp.single (toPointMap S.unop ≫ x) (1 : ℤ)) ⊗ₜ[ℤ] m) =
    b S.unop (toPointMap S.unop ≫ x) m
  rw [TensorProduct.lift.tmul]
  rw [Finsupp.lift_apply]
  rw [Finsupp.sum_single_index]
  · simp [freeTensorSectionHom]
  · apply LinearMap.ext
    intro y
    rw [LinearMap.smul_apply]
    let mod : Module ℤ (C.obj.obj S) := (C.obj.obj S).isModule
    change mod.toDistribMulAction.smul 0
        ((b S.unop (freeTensorSectionHom X S (toPointMap S.unop ≫ x))) y) = 0
    exact mod.zero_smul ((b S.unop (freeTensorSectionHom X S (toPointMap S.unop ≫ x))) y)

/-- For a sheaf, the inverse to the sheafification counit is the sheafification unit. -/
lemma sheafification_counit_inv_hom (B : LightCondAb) :
    let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
    let cB : L.obj B.obj ⟶ B :=
      (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
    (inv cB).hom = CategoryTheory.toSheafify (coherentTopology LightProfinite) B.obj := by
  intro L cB
  haveI : IsIso cB := by
    dsimp [cB, L]
    exact isIso_sheafificationAdjunction_counit B
  apply (cancel_mono cB.hom).1
  change (inv cB ≫ cB).hom =
    CategoryTheory.toSheafify (coherentTopology LightProfinite) B.obj ≫ cB.hom
  rw [IsIso.inv_hom_id]
  dsimp [cB]
  rw [CategoryTheory.sheafificationAdjunction_counit_app_val]
  rw [CategoryTheory.toSheafify_sheafifyLift]

/-- The sheaf-level free tensor constructor has the expected point slices. -/
lemma freeTensorDescLin_point (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m))
    (x : LightProfinite.of PUnit.{1} ⟶ X) :
    (λ_ B).inv ≫
      (freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)) ▷ B ≫
      freeTensorDescLin X B C b hnat =
    freeTensorFamilyMap X B C b hnat x := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
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
  let p : 𝟙_ LightCondAb ⟶ L.obj F :=
    freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)
  have hmove :
      (λ_ B).inv ≫ p ▷ B ≫ (L.obj F ◁ inv cB) =
        inv cB ≫ (λ_ (L.obj G)).inv ≫ p ▷ L.obj G := by
    calc
      (λ_ B).inv ≫ p ▷ B ≫ (L.obj F ◁ inv cB)
          = (λ_ B).inv ≫ (𝟙_ LightCondAb ◁ inv cB) ≫ p ▷ L.obj G := by
              rw [MonoidalCategory.whisker_exchange p (inv cB)]
      _ = inv cB ≫ (λ_ (L.obj G)).inv ≫ p ▷ L.obj G := by
              rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc (inv cB)]
  calc
    (λ_ B).inv ≫
        (freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)) ▷ B ≫
        freeTensorDescLin X B C b hnat
        = inv cB ≫ ((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
            (Functor.Monoidal.μIso L F G).hom) ≫ L.map α ≫ cC := by
            dsimp [freeTensorDescLin]
            change (λ_ B).inv ≫ p ▷ B ≫
                ((L.obj F ◁ inv cB) ≫ (Functor.Monoidal.μIso L F G).hom ≫
                  L.map α ≫ cC) =
              inv cB ≫ ((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
                (Functor.Monoidal.μIso L F G).hom) ≫ L.map α ≫ cC
            slice_lhs 1 3 => rw [hmove]
            simp [Category.assoc]
    _ = freeTensorFamilyMap X B C b hnat x := by
            apply Sheaf.hom_ext
            change (inv cB).hom ≫
                (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
                  (Functor.Monoidal.μIso L F G).hom).hom) ≫
                ((L.map α ≫ cC).hom) =
              (freeTensorFamilyMap X B C b hnat x).hom
            have hcinv := sheafification_counit_inv_hom B
            dsimp only at hcinv
            rw [hcinv]
            have hcompat := freeTensorPresheafPoint_sheafify_comp X B x
            dsimp only at hcompat
            change CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
                (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
                  (Functor.Monoidal.μIso L F G).hom).hom) =
              freeTensorPresheafPoint X B x ≫
                CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) at hcompat
            change CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
                (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
                  (Functor.Monoidal.μIso L F G).hom).hom) ≫
                ((L.map α ≫ cC).hom) =
              (freeTensorFamilyMap X B C b hnat x).hom
            rw [← Category.assoc]
            rw [hcompat]
            rw [Category.assoc]
            have hfac := freeTensorDescLin_sheafify_fac X B C b hnat
            dsimp only at hfac
            change CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
                ((L.map α ≫ cC).hom) = α at hfac
            rw [hfac]
            exact freeTensorPresheafPoint_desc X B C b hnat x

/-- The presheaf-level composite used to test maps out of a free-left tensor.  The source
`((free ℤ).obj X.toCondensed) ⊗ B` is pulled back to the sheafification of the pointwise
presheaf tensor. -/
noncomputable def freeTensorHomPresheafComposite (X : LightProfinite.{0}) (B C : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C) :
    (X.toCondensed.obj ⋙ ModuleCat.free ℤ) ⊗ B.obj ⟶ C.obj := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let g' : L.obj F ⊗ B ⟶ C := g
  exact CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
    (((Functor.Monoidal.μIso L F G).inv ≫ (L.obj F ◁ cB) ≫ g').hom)

/-- Evaluation of a map out of `ℤ[X] ⊗ B` on a presheaf generator
`r • [f] ⊗ m`. -/
noncomputable def freeTensorHomEval (X : LightProfinite.{0}) (B C : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    (S : LightProfinite.{0}) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    C.obj.obj ⟨S⟩ :=
  (freeTensorHomPresheafComposite X B C g).app ⟨S⟩ ((Finsupp.single f r) ⊗ₜ[ℤ] m)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Maps out of a free-left tensor are determined by their values on the elementary presheaf
free generators. -/
lemma freeTensorHom_ext (X : LightProfinite.{0}) (B C : LightCondAb)
    (g₁ g₂ : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    (h : ∀ (S : LightProfinite.{0}) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩),
      freeTensorHomEval X B C g₁ S f r m = freeTensorHomEval X B C g₂ S f r m) :
    g₁ = g₂ := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  haveI : IsIso cB := by
    dsimp [cB, G, L]
    exact isIso_sheafificationAdjunction_counit B
  let e : L.obj (F ⊗ G) ⟶ L.obj F ⊗ B :=
    (Functor.Monoidal.μIso L F G).inv ≫ (L.obj F ◁ cB)
  haveI : Epi e := by
    dsimp [e]
    infer_instance
  apply (cancel_epi e).1
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ C.property
  ext S z
  change (freeTensorHomPresheafComposite X B C g₁).app S z =
    (freeTensorHomPresheafComposite X B C g₂).app S z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a₁ a₂ ha₁ ha₂ =>
          simpa [TensorProduct.add_tmul] using congrArg₂ HAdd.hAdd ha₁ ha₂
      | single f r =>
          simpa [freeTensorHomEval, freeTensorSectionHom] using h S.unop
            (freeTensorSectionHom X S f) r m
  | add z₁ z₂ hz₁ hz₂ =>
      simpa [map_add] using congrArg₂ HAdd.hAdd hz₁ hz₂

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The testing composite of a map produced by `freeTensorDescLin` is its defining presheaf map. -/
lemma freeTensorHomPresheafComposite_desc (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m)) :
    freeTensorHomPresheafComposite X B C (freeTensorDescLin X B C b hnat) =
      freeTensorPresheafDescLin X B C b hnat := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let α : F ⊗ G ⟶ C.obj := freeTensorPresheafDescLin X B C b hnat
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let cC : L.obj C.obj ⟶ C :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app C
  have hfac := freeTensorDescLin_fac X B C b hnat
  dsimp only at hfac
  change (L.obj F ◁ cB) ≫ freeTensorDescLin X B C b hnat =
    (Functor.Monoidal.μIso L F G).hom ≫ L.map α ≫ cC at hfac
  dsimp [freeTensorHomPresheafComposite]
  have hsheaf := freeTensorDescLin_sheafify_fac X B C b hnat
  dsimp only at hsheaf
  change CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
      ((L.map α ≫ cC).hom) = α at hsheaf
  change CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) ≫
      (((Functor.Monoidal.μIso L F G).inv ≫
        ((L.obj F ◁ cB) ≫ freeTensorDescLin X B C b hnat)).hom) = α
  rw [hfac]
  have hμ : (Functor.Monoidal.μIso L F G).inv ≫
      ((Functor.Monoidal.μIso L F G).hom ≫ L.map α ≫ cC) = L.map α ≫ cC := by
    simp
  rw [hμ]
  exact hsheaf

/-- Evaluation of `freeTensorDescLin` on an elementary generator. -/
lemma freeTensorHomEval_desc (X : LightProfinite.{0}) (B C : LightCondAb)
    (b : ∀ S : LightProfinite.{0}, (S ⟶ X) → (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩))
    (hnat : ∀ {S T : LightProfinite.{0}} (g : T ⟶ S) (f : S ⟶ X)
      (m : B.obj.obj ⟨S⟩),
      C.obj.map g.op (b S f m) = b T (g ≫ f) (B.obj.map g.op m))
    (S : LightProfinite.{0}) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B C (freeTensorDescLin X B C b hnat) S f r m = r • b S f m := by
  rw [freeTensorHomEval, freeTensorHomPresheafComposite_desc]
  letI hC : @SMulCommClass ℤ ℤ (↑(C.obj.obj ⟨S⟩))
      (C.obj.obj ⟨S⟩).isModule.toDistribMulAction.toSMul
      (C.obj.obj ⟨S⟩).isModule.toDistribMulAction.toSMul :=
    intModuleCatModuleSMulComm (C.obj.obj ⟨S⟩)
  letI : Module ℤ (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩) :=
    @LinearMap.module ℤ ℤ ℤ (B.obj.obj ⟨S⟩) (C.obj.obj ⟨S⟩) _ _ _ _ _ _
      (RingHom.id ℤ) _ _ hC
  change (TensorProduct.lift
      ((Finsupp.lift (B.obj.obj ⟨S⟩ →ₗ[ℤ] C.obj.obj ⟨S⟩) ℤ
        (X.toCondensed.obj.obj ⟨S⟩)) fun f' => b S (freeTensorSectionHom X ⟨S⟩ f')))
      ((Finsupp.single f r) ⊗ₜ[ℤ] m) = r • b S f m
  rw [TensorProduct.lift.tmul]
  rw [Finsupp.lift_apply]
  rw [Finsupp.sum_single_index]
  · have hf : freeTensorSectionHom X (Opposite.op S) f = f := rfl
    rw [hf]
    rw [LinearMap.smul_apply]
    simpa [RingHom.id_apply] using
      (Int.cast_smul_eq_zsmul (R := ℤ) r ((b S f) m))
  · apply LinearMap.ext
    intro y
    rw [LinearMap.smul_apply]
    let mod : Module ℤ (C.obj.obj ⟨S⟩) := (C.obj.obj ⟨S⟩).isModule
    change mod.toDistribMulAction.smul 0 ((b S f) y) = 0
    exact mod.zero_smul ((b S f) y)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at a constant point of the free variable is the corresponding point slice. -/
lemma freeTensorHomEval_point_one (X : LightProfinite.{0}) (B C : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    (x : LightProfinite.of PUnit.{1} ⟶ X)
    (S : LightProfinite.{0}) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B C g S (toPointMap S ≫ x) 1 m =
      (((λ_ B).inv ≫
        (freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)) ▷ B ≫
          g).hom.app ⟨S⟩ m) := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let p : 𝟙_ LightCondAb ⟶ L.obj F :=
    freePointIsoUnit.inv ≫ (free ℤ).map (lightProfiniteToLightCondSet.map x)
  have hmove :
      (λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫ (L.obj F ◁ cB) =
        cB ≫ (λ_ B).inv ≫ p ▷ B := by
    calc
      (λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫ (L.obj F ◁ cB)
          = (λ_ (L.obj G)).inv ≫ (𝟙_ LightCondAb ◁ cB) ≫ p ▷ B := by
              rw [MonoidalCategory.whisker_exchange p cB]
      _ = cB ≫ (λ_ B).inv ≫ p ▷ B := by
              rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc cB]
  have hcompat := freeTensorPresheafPoint_sheafify_comp X B x
  dsimp only at hcompat
  change CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
      (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
        (Functor.Monoidal.μIso L F G).hom).hom) =
    freeTensorPresheafPoint X B x ≫
      CategoryTheory.toSheafify (coherentTopology LightProfinite) (F ⊗ G) at hcompat
  have hpresheaf :
      freeTensorPresheafPoint X B x ≫ freeTensorHomPresheafComposite X B C g =
        ((λ_ B).inv ≫ p ▷ B ≫ g).hom := by
    dsimp [freeTensorHomPresheafComposite]
    rw [← Category.assoc]
    rw [← hcompat]
    simp only [Category.assoc]
    have hμ : ((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
        (Functor.Monoidal.μIso L F G).hom ≫
        (Functor.Monoidal.μIso L F G).inv ≫ (L.obj F ◁ cB) ≫ g) =
        ((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫ (L.obj F ◁ cB) ≫ g) := by
      simp [Category.assoc]
    change CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
        (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫
          (Functor.Monoidal.μIso L F G).hom ≫
          (Functor.Monoidal.μIso L F G).inv ≫ (L.obj F ◁ cB) ≫ g).hom) =
      ((λ_ B).inv ≫ p ▷ B ≫ g).hom
    rw [hμ]
    have hmove_g :
        (λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫ (L.obj F ◁ cB) ≫ g =
          cB ≫ (λ_ B).inv ≫ p ▷ B ≫ g := by
      simpa [Category.assoc] using congrArg (fun q => q ≫ g) hmove
    calc
      CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
          (((λ_ (L.obj G)).inv ≫ p ▷ L.obj G ≫ (L.obj F ◁ cB) ≫ g).hom)
          = CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫
              ((cB ≫ (λ_ B).inv ≫ p ▷ B ≫ g).hom) := by
              exact congrArg (fun q => CategoryTheory.toSheafify
                (coherentTopology LightProfinite) G ≫ q.hom) hmove_g
      _ = ((λ_ B).inv ≫ p ▷ B ≫ g).hom := by
              change CategoryTheory.toSheafify (coherentTopology LightProfinite) G ≫ cB.hom ≫
                  (((λ_ B).inv ≫ p ▷ B ≫ g).hom) =
                ((λ_ B).inv ≫ p ▷ B ≫ g).hom
              dsimp [cB]
              rw [CategoryTheory.sheafificationAdjunction_counit_app_val]
              rw [← Category.assoc]
              rw [CategoryTheory.toSheafify_sheafifyLift]
              rw [Category.id_comp]
  dsimp [freeTensorHomEval]
  have happ := congrArg (fun η => η.app ⟨S⟩ m) hpresheaf
  let fS : X.toCondensed.obj.obj ⟨S⟩ := toPointMap S ≫ x
  change (freeTensorHomPresheafComposite X B C g).app ⟨S⟩
      (((TensorProduct.mk ℤ ((X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj ⟨S⟩)
        (B.obj.obj ⟨S⟩)) (Finsupp.single fS (1 : ℤ))) m) = _
  exact happ

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The testing evaluation on unit generators is natural in the test profinite set. -/
lemma freeTensorHomEval_naturality_one (X : LightProfinite.{0}) (B C : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    {S T : LightProfinite.{0}} (u : T ⟶ S) (f : S ⟶ X)
    (m : B.obj.obj ⟨S⟩) :
    C.obj.map u.op (freeTensorHomEval X B C g S f 1 m) =
      freeTensorHomEval X B C g T (u ≫ f) 1 (B.obj.map u.op m) := by
  let η := freeTensorHomPresheafComposite X B C g
  let fS : X.toCondensed.obj.obj ⟨S⟩ := f
  let fT : X.toCondensed.obj.obj ⟨T⟩ := u ≫ f
  have hn := ConcreteCategory.congr_hom (η.naturality u.op)
      ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)
  dsimp [freeTensorHomEval]
  calc
    C.obj.map u.op (η.app ⟨S⟩ ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m))
        = η.app ⟨T⟩
            ((((ModuleCat.free ℤ).map (X.toCondensed.obj.map u.op)) ⊗ₘ B.obj.map u.op)
              ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)) := by
            exact hn.symm
    _ = η.app ⟨T⟩ ((Finsupp.single fT (1 : ℤ)) ⊗ₜ[ℤ] (B.obj.map u.op m)) := by
            change η.app ⟨T⟩
              (((Finsupp.lmapDomain ℤ ℤ (X.toCondensed.obj.map u.op))
                  (Finsupp.single fS (1 : ℤ))) ⊗ₜ[ℤ] (B.obj.map u.op m)) =
                η.app ⟨T⟩ ((Finsupp.single fT (1 : ℤ)) ⊗ₜ[ℤ] (B.obj.map u.op m))
            rw [Finsupp.lmapDomain_apply]
            rw [Finsupp.mapDomain_single]
            rfl

/-- A coefficient on the free generator acts by the same integer on the testing evaluation. -/
lemma freeTensorHomEval_zsmul (X : LightProfinite.{0}) (B C : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    (S : LightProfinite.{0}) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B C g S f r m =
      r • freeTensorHomEval X B C g S f 1 m := by
  let η := freeTensorHomPresheafComposite X B C g
  let fS : X.toCondensed.obj.obj ⟨S⟩ := f
  dsimp [freeTensorHomEval]
  change η.app ⟨S⟩ ((Finsupp.single fS r) ⊗ₜ[ℤ] m) =
    r • η.app ⟨S⟩ ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)
  have hsingle :
      (Finsupp.single fS r : (X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj ⟨S⟩) =
      r • (Finsupp.single fS (1 : ℤ) :
        (X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj ⟨S⟩) := by
    ext y
    by_cases hy : y = fS <;> simp [hy]
  rw [hsingle]
  change η.app ⟨S⟩
      (((r • (Finsupp.single fS (1 : ℤ) :
        (X.toCondensed.obj ⋙ ModuleCat.free ℤ).obj ⟨S⟩)) ⊗ₜ[ℤ] m)) =
    r • η.app ⟨S⟩ ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)
  rw [← TensorProduct.smul_tmul']
  change (ModuleCat.Hom.hom (η.app ⟨S⟩))
      (r • ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)) =
    r • η.app ⟨S⟩ ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)
  rw [LinearMap.map_smul]
  simpa [RingHom.id_apply] using
    (Int.cast_smul_eq_zsmul (R := ℤ) r
      (η.app ⟨S⟩ ((Finsupp.single fS (1 : ℤ)) ⊗ₜ[ℤ] m)))

end ProjectiveGeneratorProof
end Solid
end LightCondensed
