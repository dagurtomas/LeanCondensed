/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Order.CompletePartialOrder

universe w

noncomputable section

namespace CategoryTheory

open Functor

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
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

@[simp]
lemma inverseDirectImageAdjunction_unit_app_val (X : Sheaf J A) :
    ((inverseDirectImageAdjunction J K A F).unit.app X).val =
    F.op.lanUnit.app X.val ≫ whiskerLeft F.op (toSheafify K (F.op.lan.obj X.val)) := by
  change ((sheafToPresheaf J A).map ((inverseDirectImageAdjunction J K A F).unit.app X)) = _
  simp [inverseDirectImageAdjunction, -sheafToPresheaf_map]

lemma inverseDirectImageAdjunction_unit_app_val_app (X : Sheaf J A) (Y : C) :
    ((inverseDirectImageAdjunction J K A F).unit.app X).val.app ⟨Y⟩ =
    (F.op.lanUnit.app X.val).app ⟨Y⟩ ≫ (toSheafify K (F.op.lan.obj X.val)).app ⟨F.obj Y⟩ := by
  simp only [Functor.id_obj, Functor.comp_obj, sheafToPresheaf_obj,
    inverseDirectImageAdjunction_unit_app_val, whiskeringLeft_obj_obj, NatTrans.comp_app,
    Functor.op_obj, whiskerLeft_app]

@[simp]
lemma inverseDirectImageAdjunction_counit_app (X : Sheaf K A) :
    ((inverseDirectImageAdjunction J K A F).counit.app X) =
    (presheafToSheaf K A).map ((F.op.lanAdjunction A).counit.app X.val) ≫
      (sheafificationAdjunction K A).counit.app X := by
  change (𝟭 (Sheaf K A)).map ((inverseDirectImageAdjunction J K A F).counit.app X) = _
  simp only [Functor.comp_obj, sheafToPresheaf_obj, Functor.id_obj, inverseDirectImageAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app, Iso.refl_inv, NatTrans.id_app,
    whiskeringLeft_obj_obj, Functor.comp_map, Category.id_comp]
  erw [Functor.map_id, Functor.map_id]
  simp

abbrev pointTopology : GrothendieckTopology PUnit := ⊥

def equivPresheafUnderlying : PUnitᵒᵖ ⥤ A ≌ A where
  functor := {
    obj := fun F ↦ F.obj ⟨PUnit.unit⟩
    map := fun f ↦ f.app _  }
  inverse := Functor.const _
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun ⟨⟨⟩⟩ ↦ Iso.refl _) ?_) ?_
    · intro ⟨⟨⟩⟩ ⟨⟨⟩⟩ _
      simp [← Functor.map_id]
      rfl
    · aesop
  counitIso := Iso.refl _

def equivSheafPresheaf : Sheaf pointTopology A ≌ PUnitᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse := {
    obj := fun F ↦ ⟨F, fun _ ↦ Presieve.isSheaf_bot⟩
    map := fun f ↦ ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory

namespace CategoryTheory.Sheaf

open Limits

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (t : C) (ht : IsTerminal t)
  (A : Type*) [Category A]  [HasWeakSheafify J A] -- [HasWeakSheafify J A]

variable [∀ (G : PUnit.{w+1}ᵒᵖ ⥤ A), ((Functor.const _).obj t).op.HasLeftKanExtension G]

instance : ((Functor.const _).obj t).IsContinuous pointTopology J where
  op_comp_isSheaf_of_types _ := by exact Presieve.isSheaf_bot

def iso₁ : ((Functor.const _).obj t).sheafPushforwardContinuous A pointTopology J ⋙
    (equivSheafPresheaf A).functor ⋙ (equivPresheafUnderlying A).functor ≅
    (sheafSections J A).obj ⟨t⟩ := sorry

end CategoryTheory.Sheaf
