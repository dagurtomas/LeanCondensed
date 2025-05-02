import Mathlib

namespace CategoryTheory

open GrothendieckTopology CategoryTheory Limits Opposite Monoidal MonoidalCategory

section FunctorCategory

set_option maxHeartbeats 300000 in
instance {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.LaxMonoidal] :
    ((whiskeringRight C D E).obj L).LaxMonoidal where
  ε' := { app X := Functor.LaxMonoidal.ε L }
  μ' F G := { app X := Functor.LaxMonoidal.μ L (F.obj X) (G.obj X) }

set_option maxHeartbeats 300000 in
instance {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.OplaxMonoidal] :
    ((whiskeringRight C D E).obj L).OplaxMonoidal where
  η' := { app X := Functor.OplaxMonoidal.η L }
  δ' F G := { app X := Functor.OplaxMonoidal.δ L (F.obj X) (G.obj X) }
  oplax_left_unitality' := by aesop -- `aesop_cat` fails for some reason
  oplax_right_unitality' := by aesop -- `aesop_cat` fails for some reason

instance {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory D]
    [MonoidalCategory E] (L : D ⥤ E) [L.Monoidal] : ((whiskeringRight C D E).obj L).Monoidal where
  ε_η := by ext; exact Functor.Monoidal.ε_η
  η_ε := by ext; exact Functor.Monoidal.η_ε
  μ_δ _ _ := by ext; exact Functor.Monoidal.μ_δ _ _
  δ_μ _ _ := by ext; exact Functor.Monoidal.δ_μ _ _

end FunctorCategory

section MonoidalFunctorTransport

variable {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]

open Functor.Monoidal

def coreMonoidalTransport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.CoreMonoidal where
  εIso := εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, μIso_hom, comp_whiskerRight,
      Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [← i.hom.naturality, map_associator_assoc, Functor.OplaxMonoidal.associativity_assoc,
      whiskerLeft_δ_μ_assoc, δ_μ_assoc]
    simp only [← Category.assoc]
    congr 1
    slice_lhs 3 4 =>
      rw [← tensorHom_id, ← tensor_comp]
      simp only [Iso.hom_inv_id_app, Category.id_comp, id_tensorHom]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    simp only [tensor_whiskerLeft, Functor.LaxMonoidal.associativity, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_id, associator_naturality_assoc]
    simp [← id_tensorHom, ← tensorHom_id, ← tensor_comp, ← tensor_comp_assoc]
  left_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← tensorHom_id, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, ← tensor_comp_assoc, Iso.hom_inv_id_app, Category.comp_id,
      Category.id_comp]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), tensor_comp]
    simp
  right_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← id_tensorHom, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, ← tensor_comp_assoc, Category.id_comp, Iso.hom_inv_id_app,
      Category.comp_id]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X), ← Category.id_comp (Functor.LaxMonoidal.ε F),
      tensor_comp]
    simp

def monoidalTransport  {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.Monoidal :=
  (coreMonoidalTransport i).toMonoidal

end MonoidalFunctorTransport

namespace Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable {E : Type*} [Category E] [MonoidalCategory E] (F : LocalizedMonoidal L W ε ⥤ E)
    [(L' ⋙ F).Monoidal]

def functorCoremonoidalOfComp : F.CoreMonoidal where
  εIso := sorry
  μIso := sorry
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

def functorMonoidalOfComp : F.Monoidal := (functorCoremonoidalOfComp L W ε F).toMonoidal

end CategoryTheory.Localization.Monoidal
-- All of the above should together imply that `Condensed.free R` is monoidal
