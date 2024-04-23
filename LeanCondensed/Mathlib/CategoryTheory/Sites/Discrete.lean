import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.InducedTopology

namespace CategoryTheory

universe v u w

open Limits Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{max u v} A]
  [HasWeakSheafify J A]
  {t : C} (ht : IsTerminal t)

namespace Sheaf

class IsDiscrete' (F : Sheaf J A) : Prop where
  memEssImageDiscrete : F ∈ (constantSheaf J A).essImage

theorem isDiscrete_iff_isIso_counit [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
    (F : Sheaf J A) : IsDiscrete' J A F ↔ IsIso ((constantSheafAdj _ _ ht).counit.app F) := by
  refine ⟨fun ⟨_⟩ ↦ ?_, fun _ ↦ ⟨?_⟩⟩
  · rwa [isIso_counit_app_iff_mem_essImage (constantSheafAdj _ _ ht)]
  · rwa [← isIso_counit_app_iff_mem_essImage (constantSheafAdj _ _ ht)]

-- theorem isDiscrete_iff_exists_iso_discrete [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
--     (F : Sheaf J A) : IsDiscrete J A ht F ↔
--     ∃ (G : Sheaf J A) (_ : IsDiscrete J A ht G), Nonempty (F ≅ G) := by
--   constructor
--   · intro h
--     refine ⟨F, h, ⟨Iso.refl _⟩⟩
--   · rintro ⟨G, h, ⟨i⟩⟩
--     rw [isDiscrete_iff_exists_iso]
--     exact ⟨i ≪≫ (asIso ((constantSheafAdj _ _ ht).counit.app G)).symm ≪≫ Functor.mapIso _ i.symm⟩

-- instance (X : A)  [(constantSheaf J A).Full] [(constantSheaf J A).Faithful] :
--     IsDiscrete J A ht <| (constantSheaf J A).obj X := by
--   rw [isDiscrete_iff_exists_iso]
--   exact ⟨(constantSheaf J A).mapIso (asIso ((constantSheafAdj _ _ ht).unit.app X))⟩

-- theorem isDiscrete_iff_exists_iso_image [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
--     (F : Sheaf J A) : IsDiscrete J A ht F ↔
--     ∃ (X : A), Nonempty (F ≅ (constantSheaf J A).obj X) := by
--   constructor
--   · intro h
--     exact ⟨((sheafSections J A).obj (op t)).obj F,
--       ⟨(asIso ((constantSheafAdj _ _ ht).counit.app F)).symm⟩⟩
--   · rintro ⟨X, h⟩
--     rw [isDiscrete_iff_exists_iso_discrete]
--     exact ⟨(constantSheaf J A).obj X, inferInstance, h⟩

-- instance (F : Sheaf J A) [IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val] :
--     IsDiscrete J A ht F where
--   isIsoCounit :=
--     let i := asIso ((constantSheafAdj J A ht).counit.app F).val
--     (inferInstance : IsIso ((sheafToPresheaf J A).preimageIso i).hom)

-- instance (F : Sheaf J A) [IsDiscrete J A ht F] :
--     IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val :=
--   let i := asIso ((constantSheafAdj J A ht).counit.app F)
--   (inferInstance : IsIso ((sheafToPresheaf J A).mapIso i).hom)

-- theorem isDiscrete_iff_isIso_counit_app_val (F : Sheaf J A) : IsDiscrete J A ht F ↔
--     (IsIso <| ((constantSheafAdj _ _ ht).counit.app F).val) :=
--   ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

-- variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
-- variable [HasLimits A] (G : C ⥤ D) [G.Full] [G.Faithful]
--   [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K] (ht' : IsTerminal (G.obj t))

-- open Functor.IsCoverDense

-- lemma isDiscrete_iff (F : Sheaf K A) :
--     let e : Sheaf J A ≌ Sheaf K A :=
--       sheafEquivOfCoverPreservingCoverLifting G J K A
--     IsDiscrete J A ht (e.inverse.obj F) ↔ IsDiscrete K A ht' F := by
--   intro e
--   have := ((constantSheafAdj K A ht').leftAdjointUniq_hom_counit
--       ((constantSheafAdj J A ht).comp e.toAdjunction)).symm
--   refine ⟨fun ⟨_⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
--   · rw [this]
--     refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
--     simp only [Functor.comp_obj, Functor.flip_obj_obj, sheafToPresheaf_obj, Functor.id_obj,
--       Adjunction.comp, Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit,
--       NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app, whiskerRight_app]
--     exact @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _) inferInstance
--   · rw [this] at h
--     refine @isIso_of_reflects_iso _ _ _ _ _ _ _ e.functor ?_ _
--     have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ ?_ h
--     · simp only [Functor.comp_obj, Functor.flip_obj_obj, sheafToPresheaf_obj, Functor.id_obj,
--         Adjunction.comp, Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit,
--         NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app, whiskerRight_app] at this
--       erw [Category.id_comp] at this
--       refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ ?_ this
--       apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso
--       exact (IsIso.of_iso _ : IsIso e.counitIso.hom)
--     · apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso
--       apply (config := { allowSynthFailures := true }) isIso_whiskerLeft
--       exact IsIso.of_iso _

-- noncomputable example :
--     let e : Sheaf J A ≌ Sheaf K A :=
--       sheafEquivOfCoverPreservingCoverLifting G J K A
--     e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
--   Iso.refl _

-- noncomputable example :
--     let e : Sheaf J A ≌ Sheaf K A :=
--       sheafEquivOfCoverPreservingCoverLifting G J K A
--     constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
--   let e : Sheaf J A ≌ Sheaf K A :=
--       sheafEquivOfCoverPreservingCoverLifting G J K A
--   (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
--     (constantSheafAdj K A ht'))

class IsDiscrete (F : Sheaf J A) : Prop where
  isIsoCounit : IsIso <| (constantSheafAdj _ _ ht).counit.app F

attribute [instance] IsDiscrete.isIsoCounit

instance (X : A) :
    IsSplitEpi <| (constantSheafAdj _ _ ht).counit.app ((constantSheaf J A).obj X) := by
  constructor
  use (constantSheaf J A).map ((constantSheafAdj _ _ ht).unit.app X)
  simp

theorem isDiscrete_iff_exists_iso [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
    (F : Sheaf J A) : IsDiscrete J A ht F ↔
    Nonempty (F ≅ (constantSheaf J A).obj (((sheafSections J A).obj (op t)).obj F)) :=
  ⟨fun _ ↦ ⟨(asIso <| (constantSheafAdj _ _ ht).counit.app F).symm⟩,
    fun ⟨i⟩ ↦ ⟨isIso_counit_app_of_iso (constantSheafAdj _ _ ht) i⟩⟩

theorem isDiscrete_iff_exists_iso_discrete [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
    (F : Sheaf J A) : IsDiscrete J A ht F ↔
    ∃ (G : Sheaf J A) (_ : IsDiscrete J A ht G), Nonempty (F ≅ G) := by
  constructor
  · intro h
    refine ⟨F, h, ⟨Iso.refl _⟩⟩
  · rintro ⟨G, h, ⟨i⟩⟩
    rw [isDiscrete_iff_exists_iso]
    exact ⟨i ≪≫ (asIso ((constantSheafAdj _ _ ht).counit.app G)).symm ≪≫ Functor.mapIso _ i.symm⟩

instance (X : A)  [(constantSheaf J A).Full] [(constantSheaf J A).Faithful] :
    IsDiscrete J A ht <| (constantSheaf J A).obj X := by
  rw [isDiscrete_iff_exists_iso]
  exact ⟨(constantSheaf J A).mapIso (asIso ((constantSheafAdj _ _ ht).unit.app X))⟩

theorem isDiscrete_iff_exists_iso_image [(constantSheaf J A).Full] [(constantSheaf J A).Faithful]
    (F : Sheaf J A) : IsDiscrete J A ht F ↔
    ∃ (X : A), Nonempty (F ≅ (constantSheaf J A).obj X) := by
  constructor
  · intro h
    exact ⟨((sheafSections J A).obj (op t)).obj F,
      ⟨(asIso ((constantSheafAdj _ _ ht).counit.app F)).symm⟩⟩
  · rintro ⟨X, h⟩
    rw [isDiscrete_iff_exists_iso_discrete]
    exact ⟨(constantSheaf J A).obj X, inferInstance, h⟩

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

open Functor.IsCoverDense

lemma isDiscrete_iff (F : Sheaf K A) :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
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
      sheafEquivOfCoverPreservingCoverLifting G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
    (constantSheafAdj K A ht'))

end CategoryTheory.Sheaf
