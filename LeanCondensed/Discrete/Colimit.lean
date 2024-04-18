import LeanCondensed.Discrete.Extend
import LeanCondensed.Mathlib.Condensed.Discrete.LocallyConstant

universe u

noncomputable section

open CategoryTheory Functor Limits Condensed FintypeCat StructuredArrow Condensed.LocallyConstant

attribute [local instance] FintypeCat.discreteTopology

namespace Condensed

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
    (c : Cone <| F ⋙ toProfinite)

section LocallyConstantAsColimit

open Profinite.Extend

variable (X : Type (u+1))

abbrev locallyConstantPresheaf : Profiniteᵒᵖ ⥤ Type _ :=
  profiniteToCompHaus.op ⋙ LocallyConstant.functorToPresheaves.obj X

noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [∀ i, Epi (c.π.app i)] :
    IsColimit <| (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i) = fj.comap (c.π.app j))
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp only [comp_obj, op_obj, Opposite.unop_op, profiniteToCompHaus_obj,
      functorToPresheaves_obj_obj, toProfinite_obj_toCompHaus_toTop_α, Functor.comp_map, op_map,
      Quiver.Hom.unop_op, profiniteToCompHaus_map, functorToPresheaves_obj_map]
    apply DFunLike.ext
    intro x'
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x'
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    rwa [c.w, c.w]

variable (S : Profinite)

noncomputable def isColimitLocallyConstantPresheafDiagram :
    IsColimit <| (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

end LocallyConstantAsColimit

section LanPresheaf

@[simps!]
def lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

@[simps!]
def lanPresheafUnit (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :
    toProfinite.op ⋙ F ⟶ toProfinite.op ⋙ lanPresheaf F :=
  pointwiseLeftKanExtensionUnit _ _

instance (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :
    IsLeftKanExtension (lanPresheaf F) (lanPresheafUnit F) := by
  dsimp [lanPresheaf, lanPresheafUnit]
  infer_instance

variable {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G)

-- TODO: generalise and PR
def lanPresheafIso : lanPresheaf F ≅ lanPresheaf G where
  hom := descOfIsLeftKanExtension _ (lanPresheafUnit F) (lanPresheaf G) (i.hom ≫ lanPresheafUnit G)
  inv := descOfIsLeftKanExtension _ (lanPresheafUnit G) (lanPresheaf F) (i.inv ≫ lanPresheafUnit F)
  hom_inv_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf F) (α := lanPresheafUnit F)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)
      (G := lanPresheaf G) (β := i.hom ≫ lanPresheafUnit G), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)]
    simp
  inv_hom_id := by
    apply hom_ext_of_isLeftKanExtension (F' := lanPresheaf G) (α := lanPresheafUnit G)
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.comp_id]
    rw [← Category.assoc, descOfIsLeftKanExtension_fac (α := lanPresheafUnit G)
      (G := lanPresheaf F) (β := i.inv ≫ lanPresheafUnit F), Category.assoc,
      descOfIsLeftKanExtension_fac (α := lanPresheafUnit F)]
    simp

end LanPresheaf

section ColimitLocallyConstant

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
  (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)

variable (S : Profinite.{u})

def functorToPresheaves_iso_colimit :
    colimit ((Profinite.Extend.functorOp S.asLimitCone) ⋙
      ((CostructuredArrow.proj toProfinite.op ⟨S⟩) ⋙ toProfinite.op ⋙ F)) ≅ F.obj ⟨S⟩ :=
  (colimit.isColimit _).coconePointUniqueUpToIso (hF S)

instance (S : Profinite) : Final <|
    Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

def functorToPresheaves_iso_colimit_lan :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    functorToPresheaves_iso_colimit F hF S

@[simp]
lemma functorToPresheaves_iso_colimit_lan_hom : (functorToPresheaves_iso_colimit_lan F hF S).hom =
    colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp only [lanPresheaf_obj, comp_obj, op_obj, profiniteToCompHaus_obj,
    functorToPresheaves_obj_obj, Opposite.unop_op, functorToPresheaves_iso_colimit_lan,
    Final.colimitIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, colimit.pre_desc]
  rfl

def lanPresheaf_iso_functorToPresheaves : lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ ↦ (functorToPresheaves_iso_colimit_lan F hF S)) fun _ ↦ ?_
  simp only [lanPresheaf_obj, comp_obj, op_obj, profiniteToCompHaus_obj,
    functorToPresheaves_obj_obj, Opposite.unop_op,
    functorToPresheaves_iso_colimit_lan_hom, Functor.comp_map, op_map,
    profiniteToCompHaus_map, lanPresheaf, lan_obj_map, colimit.pre_desc]
  exact colimit.hom_ext fun _ ↦ (by simp)

end ColimitLocallyConstant

def lanPresheaf_iso_functorToPresheaves' (X : Type (u+1)) :
    lanPresheaf (profiniteToCompHaus.op ⋙ functorToPresheaves.{u+1, u}.obj X) ≅
    profiniteToCompHaus.op ⋙ functorToPresheaves.obj X :=
  lanPresheaf_iso_functorToPresheaves
    (profiniteToCompHaus.op ⋙ functorToPresheaves.{u+1, u}.obj X)
    fun _ ↦ isColimitLocallyConstantPresheafDiagram _ _

def lanCondensedSet' (X : Type (u+1)) : Sheaf (coherentTopology Profinite.{u}) (Type (u+1)) where
  val := lanPresheaf (profiniteToCompHaus.op ⋙ functorToPresheaves.obj X)
  cond := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheaf_iso_functorToPresheaves' X)]
    exact (LocallyConstant.functor.obj X).isSheafProfinite

def lanCondensedSet (X : Type (u+1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanCondensedSet' X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
  [PreservesFiniteProducts F]

open Opposite

@[simps]
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u+1) where
  obj X := X.unop → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)
  map f g := g ∘ f.unop

def finYonedaIso :
    toProfinite.op ⋙ profiniteToCompHaus.op ⋙ functorToPresheaves.obj (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) ≅
    finYoneda F := by
  refine NatIso.ofComponents ?_ ?_
  · intro Y
    exact {
      hom := fun f ↦ f.toFun
      inv := fun f ↦ ⟨f, (by
        have : DiscreteTopology (profiniteToCompHaus.obj (toProfinite.op.obj Y).unop) := by
          simp only [profiniteToCompHaus, toProfinite, Profinite.of, op_obj, Opposite.unop_op,
            inducedFunctor_obj]
          infer_instance
        exact IsLocallyConstant.of_discrete _
        )⟩
      hom_inv_id := by aesop
      inv_hom_id := by aesop
    }
  · aesop

def mapOfElement {X : FintypeCat} (x : X) : of (PUnit.{u+1}) ⟶ X := fun _ ↦ x

def fintypeCatAsCofan (X : FintypeCat) :
    Cofan (fun (_ : X) ↦ toProfinite.obj (of (PUnit.{u+1}))) :=
  Cofan.mk (toProfinite.obj X) (fun x ↦ toProfinite.map (mapOfElement x))

def isoCoproduct' {X : FintypeCat} : toProfinite.obj X ≅
    ∐ (fun (x : X) ↦ toProfinite.obj (of (PUnit.{u+1}))) := by
  sorry

def isoCoproduct {X : FintypeCat} : toProfinite.op.obj ⟨X⟩ ≅
    ∏ (fun (x : X) ↦ toProfinite.op.obj ⟨of (PUnit.{u+1})⟩) := by
  dsimp only [op_obj]
  sorry

def finYonedaIso'_components (X : FintypeCat) :
    F.obj (toProfinite.op.obj ⟨X⟩) ≅ (X → F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) where
  hom f x := (toProfinite.op ⋙ F).map (mapOfElement x).op f
  inv f := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

def finYonedaIso' : toProfinite.op ⋙ F ≅ finYoneda F := sorry

def isoCompToProfinite : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ profiniteToCompHaus.op ⋙
    functorToPresheaves.obj (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  finYonedaIso' F ≪≫ (finYonedaIso F).symm

def isoLanDiscrete (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ lanPresheaf (profiniteToCompHaus.op ⋙ functorToPresheaves.obj (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))) :=
  (lanPresheaf_iso_functorToPresheaves F hF).symm ≪≫ lanPresheafIso (isoCompToProfinite F)

def isoDiscrete (hF : ∀ S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ profiniteToCompHaus.op ⋙
    functorToPresheaves.obj (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩)) :=
  isoLanDiscrete F hF ≪≫
    lanPresheaf_iso_functorToPresheaves' (F.obj (toProfinite.op.obj ⟨of PUnit.{u+1}⟩))

#exit

section SigmaComparison

open CompHaus

variable (X : CondensedSet.{u}) {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
def sigmaComparison : X.val.obj ⟨(of ((a : α) × σ a))⟩ ⟶ ((a : α) → X.val.obj ⟨of (σ a)⟩) :=
  fun x a ↦ X.val.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X.val :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  have : Fintype α := Fintype.ofFinite _
  have : Fintype α' := Fintype.ofEquiv α e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X.val

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.val.mapIso (opCoproductIsoProduct' (finiteCoproduct.isColimit.{u, u} fun a ↦ of (σ a))
      (productIsProduct fun x ↦ Opposite.op (of (σ x))))).hom ≫
    (PreservesProduct.iso X.val fun a ↦ ⟨of (σ a)⟩).hom ≫
    (Types.productIso.{u, u + 1} fun a ↦ X.val.obj ⟨of (σ a)⟩).hom := by
  ext x a
  simp only [finiteCoproduct.cocone_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply]
  have := congrFun (piComparison_comp_π X.val (fun a ↦ ⟨of (σ a)⟩) a)
  simp only [types_comp_apply] at this
  rw [this, ← FunctorToTypes.map_comp_apply]
  simp only [sigmaComparison]
  apply congrFun
  congr 2
  erw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  change finiteCoproduct.ι.{u, u} (fun a ↦ of (σ a)) _ = _
  rw [← Sigma.ι_comp_toFiniteCoproduct]
  congr
  simp only [opCoproductIsoProduct, ← unop_comp, coproductIsoCoproduct,
    opCoproductIsoProduct'_comp_self]
  rfl

instance : IsIso <| sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end SigmaComparison
