import Mathlib.CategoryTheory.Adjunction.FullyFaithful
-- TODO: Move the stuff that depends on the following imports to separate files
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.InducedTopology

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] (U : C ⥤ D)

section IsRightAdjointProp
-- Joël's refactor of `IsRightAdjoint` etc.

namespace CategoryTheory.Functor

noncomputable def leftAdjointCongr' {R : D ⥤ C} {L : C ⥤ D} (adj : L ⊣ R) :
    haveI : R.IsRightAdjoint := adj.isRightAdjoint
    L ≅ leftAdjoint R :=
  haveI : R.IsRightAdjoint := adj.isRightAdjoint
  adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint R)

noncomputable def leftAdjointCongr {F G : D ⥤ C} (i : F ≅ G) [F.IsRightAdjoint] :
    haveI := isRightAdjoint_of_iso i
    leftAdjoint F ≅ leftAdjoint G :=
  haveI := isRightAdjoint_of_iso i
  ((Adjunction.ofIsRightAdjoint F).ofNatIsoRight i).leftAdjointUniq (Adjunction.ofIsRightAdjoint G)

end CategoryTheory.Functor

end IsRightAdjointProp

namespace CategoryTheory.Functor

class HasDiscreteObjects : Prop where
  isRightAdjoint : IsRightAdjoint U := by infer_instance
  faithful : (leftAdjoint U).Faithful := by infer_instance
  full : (leftAdjoint U).Full := by infer_instance

attribute [instance] HasDiscreteObjects.isRightAdjoint
attribute [instance] HasDiscreteObjects.faithful
attribute [instance] HasDiscreteObjects.full

variable {U} in
def hasDiscreteObjectsOfNatIso {U' : C ⥤ D} (i : U ≅ U') [HasDiscreteObjects U] :
    HasDiscreteObjects U' where
  isRightAdjoint := ⟨leftAdjoint U,
    ⟨Adjunction.ofNatIsoRight (Adjunction.ofIsRightAdjoint U) i⟩⟩
  faithful := Faithful.of_iso (leftAdjointCongr i)
  full := Full.of_iso (leftAdjointCongr i)

variable {U} in
lemma hasDiscreteObjects_iff_of_natIso {U' : C ⥤ D} (i : U ≅ U') :
    HasDiscreteObjects U ↔ HasDiscreteObjects U' :=
  ⟨fun _ ↦ hasDiscreteObjectsOfNatIso i,  fun _ ↦ hasDiscreteObjectsOfNatIso i.symm⟩

def HasDiscreteObjects.mk' {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] :
    HasDiscreteObjects U where
  isRightAdjoint := adj.isRightAdjoint
  faithful := Faithful.of_iso (leftAdjointCongr' adj)
  full := Full.of_iso (leftAdjointCongr' adj)

end Functor

class IsDiscrete [U.HasDiscreteObjects] (X : C) : Prop where
  isIso_counit : IsIso <| (Adjunction.ofIsRightAdjoint U).counit.app X := by infer_instance

attribute [instance] IsDiscrete.isIso_counit

open Adjunction

theorem isDiscrete_of_iso [U.HasDiscreteObjects] {X : C} {Y : D}
    (i : X ≅ U.leftAdjoint.obj Y) : IsDiscrete U X where
  isIso_counit := isIso_counit_app_of_iso _ i

theorem isDiscrete_iff_mem_essImage {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] (X : C) :
    haveI : U.HasDiscreteObjects := Functor.HasDiscreteObjects.mk' _ adj
    IsDiscrete U X ↔ X ∈ L.essImage := by
  haveI := Functor.HasDiscreteObjects.mk' _ adj
  refine ⟨fun h ↦ ⟨U.obj X, ⟨?_⟩⟩, fun ⟨Y, ⟨i⟩⟩ ↦ ?_⟩
  · exact (Functor.leftAdjointCongr' adj).app _ ≪≫
      asIso ((Adjunction.ofIsRightAdjoint _).counit.app _)
  · exact isDiscrete_of_iso U (i.symm ≪≫ (Functor.leftAdjointCongr' adj).app _)

theorem isDiscrete_iff_isIso_counit_app {L : D ⥤ C} (adj : L ⊣ U) [L.Full] [L.Faithful] (X : C) :
    haveI : U.HasDiscreteObjects := Functor.HasDiscreteObjects.mk' _ adj
    IsDiscrete U X ↔ IsIso (adj.counit.app X) := by
  rw [isIso_counit_app_iff_mem_essImage]
  exact isDiscrete_iff_mem_essImage _ adj _

theorem isDiscrete_congr [U.HasDiscreteObjects] {X Y : C} (i : X ≅ Y) [IsDiscrete U X] :
    IsDiscrete U Y :=
  isDiscrete_of_iso U (i.symm ≪≫ (asIso ((Adjunction.ofIsRightAdjoint U).counit.app X)).symm)

theorem isDiscrete_of_natIso [U.HasDiscreteObjects] (U' : C ⥤ D) (i : U ≅ U') (X : C)
    [IsDiscrete U X] :
    haveI : U'.HasDiscreteObjects := Functor.hasDiscreteObjectsOfNatIso i
    IsDiscrete U' X :=
  haveI : U'.HasDiscreteObjects := Functor.hasDiscreteObjectsOfNatIso i
  isDiscrete_of_iso U' ((asIso ((Adjunction.ofIsRightAdjoint U).counit.app X)).symm ≪≫
    ((Functor.leftAdjointCongr i)).app _)

end CategoryTheory

open Functor

namespace TopCat

instance : discrete.Faithful where
  map_injective h := congrArg (fun f ↦ f.toFun) h

instance : discrete.Full where
  map_surjective a := ⟨a.toFun, rfl⟩

instance : (forget TopCat).HasDiscreteObjects := HasDiscreteObjects.mk' _ adj₁

def isoDiscreteOfDiscreteTopology (X : TopCat) [DiscreteTopology X] : X ≅ discrete.obj X where
  hom := ⟨id, continuous_of_discreteTopology⟩
  inv := ⟨id, continuous_of_discreteTopology⟩

lemma isDiscrete_iff_discreteTopology (X : TopCat) :
    IsDiscrete (forget _) X ↔ DiscreteTopology X := by
  rw [isDiscrete_iff_mem_essImage (adj := adj₁)]
  constructor
  · intro ⟨_, ⟨i⟩⟩
    exact DiscreteTopology.of_continuous_injective i.inv.continuous
      ((TopCat.mono_iff_injective _).mp inferInstance)
  · intro
    exact ⟨X, ⟨(isoDiscreteOfDiscreteTopology X).symm⟩⟩

end TopCat

open Limits Opposite

namespace CategoryTheory.Sheaf

variable (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A]
  [(constantSheaf J A).Faithful] [(constantSheaf J A).Full] {t : C} (ht : IsTerminal t)

abbrev IsDiscrete (F : Sheaf J A) : Prop :=
  haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
  CategoryTheory.IsDiscrete ((sheafSections J A).obj (op t)) F

theorem isDiscrete_iff_mem_essImage (F : Sheaf J A) {t : C} (ht : IsTerminal t) :
    haveI := HasDiscreteObjects.mk' _ (constantSheafAdj J A ht)
    F.IsDiscrete J A ht ↔ F ∈ (constantSheaf J A).essImage :=
  CategoryTheory.isDiscrete_iff_mem_essImage _ (constantSheafAdj J A ht) _

section

universe w v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type w) [Category.{max u v} A]
  [HasWeakSheafify J A]
  {t : C} (ht : IsTerminal t)

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
variable [HasLimits A] (G : C ⥤ D) [G.Full] [G.Faithful]
  [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K] (ht' : IsTerminal (G.obj t))

variable [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]

open Functor.IsCoverDense

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

noncomputable def equivCommuteConstant :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  (Adjunction.leftAdjointUniq ((constantSheafAdj J A ht).comp e.toAdjunction)
    (constantSheafAdj K A ht'))

noncomputable def equivCommuteConstant' :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    constantSheaf J A ≅ constantSheaf K A ⋙ e.inverse :=
  let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
  isoWhiskerLeft (constantSheaf J A) e.unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J A ht K G ht') e.inverse

lemma isDiscrete_iff (F : Sheaf K A) :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquivOfCoverPreservingCoverLifting G J K A
    haveI : (constantSheaf K A).Faithful :=
      Functor.Faithful.of_iso (equivCommuteConstant J A ht K G ht')
    haveI : (constantSheaf K A).Full :=
      Functor.Full.of_iso (equivCommuteConstant J A ht K G ht')
    (e.inverse.obj F).IsDiscrete J A ht ↔ IsDiscrete K A ht' F := by
  intro e
  simp only [isDiscrete_iff_mem_essImage]
  constructor
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf K A).obj Y ≅ F :=
      (equivCommuteConstant J A ht K G ht').symm.app _ ≪≫ e.functor.mapIso i ≪≫ e.counitIso.app _
    exact ⟨_, ⟨j⟩⟩
  · intro ⟨Y, ⟨i⟩⟩
    let j : (constantSheaf J A).obj Y ≅ e.inverse.obj F :=
      (equivCommuteConstant' J A ht K G ht').app _ ≪≫ e.inverse.mapIso i
    exact ⟨_, ⟨j⟩⟩

end

end CategoryTheory.Sheaf
