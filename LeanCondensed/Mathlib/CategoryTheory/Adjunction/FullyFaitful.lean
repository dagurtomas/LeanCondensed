import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Opposites

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Faithful] [L.Full] {X : D} (i : X ≅ L.obj (R.obj X))

lemma isIso_counit : IsIso (adj.counit.app X : L.obj (R.obj X) ⟶ X) := by
  let D' := L.EssImageSubcategory
  let iD' : D' ⥤ D := L.essImageInclusion
  let L' : C ⥤ D' := L.toEssImage
  let R' : D' ⥤ C := iD' ⋙ R
  let comm₁ : L ≅ L' ⋙ iD' := Iso.refl _
  let comm₂ : iD' ⋙ R ≅ R' := Iso.refl _
  let adj' : L' ⊣ R' := adj.restrictFullyFaithful (𝟭 _) iD' comm₁ comm₂
  have : L'.IsEquivalence := Functor.IsEquivalence.ofFullyFaithfullyEssSurj L'
  let R'' := L'.asEquivalence.inverse
  let iR : R' ≅ R'' := adj'.rightAdjointUniq L'.asEquivalence.toAdjunction
  have hR' : R'.IsEquivalence := Functor.IsEquivalence.ofIso iR.symm inferInstance
  let X' : D' := ⟨X, ⟨R.obj X, ⟨i.symm⟩⟩⟩
  have : IsIso (adj'.counit.app X') := inferInstance
  have hh := @Functor.map_isIso _ _ _ _ _ _ iD' _ this
  convert hh
  simp only [Functor.comp_obj, Functor.id_obj, Adjunction.restrictFullyFaithful,
    equivOfFullyFaithful, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Functor.id_map,
    Adjunction.mkOfHomEquiv_counit_app, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
    Equiv.symm_symm, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply, Iso.refl_inv,
    Iso.symm_hom, Iso.app_inv, Category.id_comp, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, Iso.symm_inv, Iso.app_hom, NatTrans.id_app, Iso.refl_hom, Category.comp_id,
    Equiv.coe_fn_symm_mk, Functor.image_preimage, adj', comm₁]
  erw [Category.id_comp, Functor.map_id, Category.id_comp, Category.id_comp]
  rfl


-- PR: add this to `FullyFaithful` file, move uniqueness stuff from `Opposite` to `Basic`
