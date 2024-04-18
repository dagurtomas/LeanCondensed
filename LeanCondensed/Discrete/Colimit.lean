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

@[simps!]
def lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

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
    (fun ⟨S⟩ ↦ (functorToPresheaves_iso_colimit_lan F hF S)) ?_
  intro ⟨S⟩ ⟨T⟩ ⟨(f : T ⟶ S)⟩
  simp only [lanPresheaf_obj, comp_obj, op_obj, profiniteToCompHaus_obj,
    functorToPresheaves_obj_obj, Opposite.unop_op,
    functorToPresheaves_iso_colimit_lan_hom, Functor.comp_map, op_map,
    profiniteToCompHaus_map, lanPresheaf, lan_obj_map, colimit.pre_desc]
  apply colimit.hom_ext
  intro j
  simp

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
