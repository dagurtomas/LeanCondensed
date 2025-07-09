/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transport a symmetric monoidal structure along an equivalence of categories
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Functor.LaxBraided

variable [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D] [BraidedCategory D]

open Functor.LaxMonoidal BraidedCategory

/--
Given two lax monoidal, monoidally isomorphic functors, if one is lax braided, so is the other.
-/
def ofNatIso (F G : C ⥤ D) (i : F ≅ G) [F.LaxBraided] [G.LaxMonoidal]
    [NatTrans.IsMonoidal i.hom]  : G.LaxBraided where
  braided X Y := by
    have (X Y : C) : μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app _ := by
      simp [NatTrans.IsMonoidal.tensor X Y, ← tensor_comp_assoc]
    rw [this X Y, this Y X, ← braiding_naturality_assoc, ← Functor.LaxBraided.braided_assoc]
    simp

end CategoryTheory.Functor.LaxBraided

section

/-- Pull back a symmetric braiding along a fully faithful monoidal functor. -/
noncomputable def symmetricCategoryOfFullyFaithful {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] [F.Full]
    [F.Faithful] [SymmetricCategory D] : SymmetricCategory C :=
  let h : BraidedCategory C := braidedCategoryOfFullyFaithful F
  let _ : F.Braided := {
    braided X Y := by simp [h, braidedCategoryOfFullyFaithful, braidedCategoryOfFaithful] }
  symmetricCategoryOfFaithful F

end

namespace CategoryTheory.Monoidal

instance Transported.instBraidedCategory (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  braidedCategoryOfFullyFaithful (equivalenceTransported e).inverse

local notation "e'" e => equivalenceTransported e

instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).inverse.Braided where
  braided X Y := by
    simp [Transported.instBraidedCategory, braidedCategoryOfFullyFaithful,
      braidedCategoryOfFaithful]

instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).LaxBraided :=
  Functor.LaxBraided.ofNatIso _ _ (e' e).unitIso

instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).Braided where
  braided := Functor.LaxBraided.braided

instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).functor.Braided where
  braided X Y := by
    apply (e' e).inverse.map_injective
    have : Functor.LaxMonoidal.μ (((e' e).functor ⋙ (e' e).inverse)) X Y ≫
        ((e' e).functor ⋙ (e' e).inverse).map (β_ X Y).hom ≫
          Functor.OplaxMonoidal.δ ((e' e).functor ⋙ (e' e).inverse) Y X =
            (β_ (((e' e).functor ⋙ (e' e).inverse).obj X)
              (((e' e).functor ⋙ (e' e).inverse).obj Y)).hom := by
      simp only [((e' e).functor ⋙ (e' e).inverse).map_braiding X Y,
        Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, assoc,
        Functor.Monoidal.μ_δ, comp_id, Functor.Monoidal.μ_δ_assoc]
    simp only [Functor.comp_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Equivalence.symm_inverse, Equivalence.symm_functor,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, Functor.LaxMonoidal.comp_μ, Functor.comp_map,
      Equivalence.inv_fun_map, Functor.id_obj, Functor.OplaxMonoidal.comp_δ, assoc] at this
    simp [← this]
    sorry

instance Transported.instSymmetricCategory (e : C ≌ D) [MonoidalCategory C]
    [SymmetricCategory C] : SymmetricCategory (Transported e) :=
  symmetricCategoryOfFullyFaithful (equivalenceTransported e).inverse

end CategoryTheory.Monoidal
