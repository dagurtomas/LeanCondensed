import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Sheafification

noncomputable section

namespace CategoryTheory

@[simp]
lemma Adjunction.restrictFullyFaithful_unit_app:
      ∀ {C : Type*} [inst : CategoryTheory.Category C] {D : Type*}
        [inst_1 : CategoryTheory.Category D] {C' : Type*} [inst_2 : CategoryTheory.Category C']
        {D' : Type*} [inst_3 : CategoryTheory.Category D'] (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'}
        {R' : D' ⥤ C'} (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
        [inst_4 : CategoryTheory.Functor.Full iC] [inst_5 : CategoryTheory.Functor.Faithful iC]
        [inst_6 : CategoryTheory.Functor.Full iD] [inst_7 : CategoryTheory.Functor.Faithful iD] (X : C),
        (CategoryTheory.Adjunction.restrictFullyFaithful iC iD adj comm1 comm2).unit.app X =
          iC.preimage (adj.unit.app (iC.obj X) ≫ R'.map (comm1.hom.app X) ≫ comm2.hom.app (L.obj X)) := by simp [restrictFullyFaithful]


@[simp]
lemma Adjunction.restrictFullyFaithful_counit_app:
      ∀ {C : Type*} [inst : CategoryTheory.Category C] {D : Type*}
        [inst_1 : CategoryTheory.Category D] {C' : Type*} [inst_2 : CategoryTheory.Category C']
        {D' : Type*} [inst_3 : CategoryTheory.Category D'] (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'}
        {R' : D' ⥤ C'} (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
        [inst_4 : CategoryTheory.Functor.Full iC] [inst_5 : CategoryTheory.Functor.Faithful iC]
        [inst_6 : CategoryTheory.Functor.Full iD] [inst_7 : CategoryTheory.Functor.Faithful iD] (Y : D),
        (CategoryTheory.Adjunction.restrictFullyFaithful iC iD adj comm1 comm2).counit.app Y =
          iD.preimage (comm1.inv.app (R.obj Y) ≫ L'.map (comm2.inv.app Y) ≫ adj.counit.app (iD.obj Y)) := sorry

variable {C D : Type*} [Category C] [Category D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type*) [Category A] [HasWeakSheafify K A] -- [HasWeakSheafify J A]
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [∀ (G : Cᵒᵖ ⥤ A), F.op.HasLeftKanExtension G]

abbrev inverseImage : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ F.op.lan ⋙ presheafToSheaf K A

def inverseDirectImageAdjunction :
    inverseImage J K A F ⊣ F.sheafPushforwardContinuous A J K :=
  ((F.op.lanAdjunction A).comp (sheafificationAdjunction K A)).restrictFullyFaithful
      (sheafToPresheaf J A) (𝟭 _) (Iso.refl _) (Iso.refl _)

lemma inverseDirectImageAdjunction_unit_app_val_app (X : Sheaf J A) (Y : C) :
    ((inverseDirectImageAdjunction J K A F).unit.app X).val.app ⟨Y⟩ =
    (F.op.lanUnit.app X.val).app ⟨Y⟩ ≫ (toSheafify K (F.op.lan.obj X.val)).app ⟨(F.obj Y)⟩ := by
  simp only [Functor.id_obj, Functor.comp_obj, sheafToPresheaf_obj, inverseDirectImageAdjunction,
    Adjunction.comp, whiskeringLeft_obj_obj, Functor.lanAdjunction_unit,
    Adjunction.restrictFullyFaithful_unit_app, Functor.preimage, Functor.Full.preimage,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, sheafificationAdjunction_unit_app,
    whiskeringLeft_obj_map, Functor.associator_inv_app, Category.comp_id, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_map, sheafToPresheaf_map, Sheaf.instCategorySheaf_id_val,
    whiskerLeft_id', Functor.op_obj]
  rfl

end CategoryTheory
