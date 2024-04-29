/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Conj
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-!

# Restricting adjunctions

`Adjunction.restrictFullyFaithful` shows that an adjunction can be restricted along fully faithful
inclusions.
-/

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂ v₃ v₄ u₃ u₄

open Category Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
variable {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
variable [iC.Full] [iC.Faithful] [iD.Full] [iD.Faithful]

@[simp, reassoc]
lemma map_restrictFullyFaithful_unit_app (X : C) :
    iC.map ((restrictFullyFaithful iC iD adj comm1 comm2).unit.app X) =
    adj.unit.app (iC.obj X) ≫ R'.map (comm1.hom.app X) ≫ comm2.hom.app (L.obj X) := by
  simp [restrictFullyFaithful]

@[simp, reassoc]
lemma map_restrictFullyFaithful_counit_app (X : D) :
    iD.map ((restrictFullyFaithful iC iD adj comm1 comm2).counit.app X) =
    comm1.inv.app (R.obj X) ≫ L'.map (comm2.inv.app X) ≫ adj.counit.app (iD.obj X) := by
  dsimp [restrictFullyFaithful]
  simp

end CategoryTheory.Adjunction
