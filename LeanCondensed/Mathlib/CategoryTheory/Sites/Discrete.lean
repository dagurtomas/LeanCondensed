import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.InducedTopology
import LeanCondensed.Mathlib.CategoryTheory.Adjunction.FullyFaithful

namespace CategoryTheory

universe v u w

open Limits Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{max u v} A]
  [HasWeakSheafify J A]
  {t : C} (ht : IsTerminal t)

namespace Sheaf

class IsDiscrete (F : Sheaf J A) : Prop where
  isIsoCounit : IsIso <| (constantSheafAdj _ _ ht).counit.app F

attribute [instance] IsDiscrete.isIsoCounit

theorem isDiscrete_iff_exists_iso [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
    (F : Sheaf J A) : IsDiscrete J A ht F ↔
    Nonempty (F ≅ (constantSheaf J A).obj (((sheafSections J A).obj (op t)).obj F)) :=
  ⟨fun _ ↦ ⟨(asIso <| (constantSheafAdj _ _ ht).counit.app F).symm⟩,
    fun ⟨i⟩ ↦ ⟨(constantSheafAdj _ _ ht).isIso_counit_of_iso i⟩⟩

instance (F : Sheaf J A) [IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val] :
    IsDiscrete J A ht F where
  isIsoCounit :=
    let i := asIso ((constantSheafAdj J A ht).counit.app F).val
    (inferInstance : IsIso ((sheafToPresheaf J A).preimageIso i).hom)

instance (F : Sheaf J A) [IsDiscrete J A ht F] :
    IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val :=
  let i := asIso ((constantSheafAdj J A ht).counit.app F)
  (inferInstance : IsIso ((sheafToPresheaf J A).mapIso i).hom)

theorem isDiscrete_iff_isIso_counit_app_val (F : Sheaf J A) : IsDiscrete J A ht F ↔
    (IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
variable [HasLimits A] (G : C ⥤ D) [G.Full] [G.Faithful]
  [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K] (ht' : IsTerminal (G.obj t))

lemma isDiscrete_iff (F : Sheaf K A) :
    let e : Sheaf J A ≌ Sheaf K A :=
      Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting G J K A
    IsDiscrete J A ht (e.inverse.obj F) ↔ IsDiscrete K A ht' F := by
  intro e
  have := ((constantSheafAdj K A ht').leftAdjointUniq_hom_counit
      ((constantSheafAdj J A ht).comp e.toAdjunction)).symm
  refine ⟨fun ⟨_⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · rw [this]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
    simp only [Functor.comp_obj, Functor.flip_obj_obj, sheafToPresheaf_obj, Functor.id_obj,
      Adjunction.comp, Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit,
      NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app, whiskerRight_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _) inferInstance
  · rw [this] at h
    refine @isIso_of_reflects_iso _ _ _ _ _ _ _ e.functor ?_ _
    have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ?_ h
    · simp only [Functor.comp_obj, Functor.flip_obj_obj, sheafToPresheaf_obj, Functor.id_obj,
        Adjunction.comp, Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit,
        NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app, whiskerRight_app] at this
      erw [Category.id_comp] at this
      refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ ?_ this
      apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso
      exact (IsIso.of_iso _ : IsIso e.counitIso.hom)
    · apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso
      apply (config := { allowSynthFailures := true }) isIso_whiskerLeft
      exact IsIso.of_iso _

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A :=
      Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting G J K A
  (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
    (constantSheafAdj K A ht'))

end CategoryTheory.Sheaf
