/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Canonical

universe u

noncomputable section

open CategoryTheory Functor Sheaf GrothendieckTopology

namespace coherentTopology

variable {C : Type u} [Category C] {J : GrothendieckTopology C} [Subcanonical J]

variable (S S' : C) {A A' : (Sheaf J (Type _))}

@[simps! apply]
def yoneda (A) :
    (J.yoneda.obj S ⟶ A) ≃ A.val.obj ⟨S⟩ :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans yonedaEquiv

@[simp]
lemma yoneda_symm_apply_val_app (a : A.val.obj ⟨S⟩) (Y : Cᵒᵖ) (f : Y.unop ⟶ S) :
      ((yoneda S A).symm a).val.app Y f = A.val.map f.op a := rfl

lemma yoneda_symm_naturality {S' : C} (f : S' ⟶ S)
    (x : A.val.obj ⟨S⟩) : J.yoneda.map f ≫ (yoneda S A).symm x =
      (yoneda S' A).symm ((A.val.map f.op) x) := by
  apply Sheaf.hom_ext
  simp only [Sheaf.comp_val]
  ext T y
  simp only [FunctorToTypes.comp, yoneda_symm_apply_val_app, Opposite.op_unop]
  rw [← FunctorToTypes.map_comp_apply (F := A.val)]
  rfl

attribute [local instance] Types.instConcreteCategory Types.instFunLike
lemma yoneda_symm_conaturality (f : A ⟶ A')
    (x : A.val.obj ⟨S⟩) : (yoneda S A).symm x ≫ f = (yoneda S A').symm (f.val.app ⟨S⟩ x) := by
  apply Sheaf.hom_ext
  simp only [Sheaf.comp_val]
  ext T y
  exact NatTrans.naturality_apply (φ := f.val) (Y := T) _ _

lemma yoneda_conaturality (f : A ⟶ A')
    (g : J.yoneda.obj S ⟶ A)
  : f.val.app ⟨S⟩ (yoneda S A g) = yoneda S A' (g ≫ f) := rfl

variable {D : Type*} [Category D] {FD : D → D → Type*} {DD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)] [ConcreteCategory D FD]
  {free : Type _ ⥤ D} (adj : free ⊣ HasForget.forget)
  [HasWeakSheafify J D]
  [J.HasSheafCompose (HasForget.forget (C := D))]

variable (S S' : C)

variable (A A' : (Sheaf J) D)

abbrev forgetYoneda :
    (J.yoneda.obj S ⟶ (sheafCompose J (HasForget.forget (C := D))).obj A)
      ≃ ((A.val ⋙ HasForget.forget).obj ⟨S⟩)
  := yoneda _ _

def freeYoneda :
    ((J.yoneda ⋙ (composeAndSheafify J free)).obj S ⟶ A) ≃ ((A.val ⋙ HasForget.forget).obj ⟨S⟩)
  := ((adjunction _ adj).homEquiv _ _).trans (yoneda _ _)

lemma freeYoneda_symm_naturality {S S'} (f : S' ⟶ S)
    (x : (A.val ⋙ HasForget.forget).obj ⟨S⟩) : (J.yoneda ⋙ composeAndSheafify J free).map f ≫
      (freeYoneda adj S A).symm x = (freeYoneda adj S' A).symm ((A.val.map f.op) x) := by
  simp only [Functor.comp_obj, freeYoneda, Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [← Category.assoc]
  erw [←Functor.map_comp (composeAndSheafify _ _), yoneda_symm_naturality]
  rfl

lemma freeYoneda_symm_conaturality (f : A ⟶ A')
    (x : ((A.val ⋙ HasForget.forget).obj ⟨S⟩)) :
    (freeYoneda adj S A).symm x ≫ f = (freeYoneda adj S A').symm (f.val.app ⟨S⟩ x) := by
  simp only [freeYoneda, Equiv.symm_trans_apply]
  erw [←yoneda_symm_conaturality S
    (A := (sheafCompose J (HasForget.forget (C := D))).obj A)
    (f := (sheafCompose J (HasForget.forget (C := D))).map f)
  ]
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Category.assoc, Functor.comp_obj, Functor.map_comp]
  erw [Adjunction.counit_naturality (adjunction J adj) f]
  rfl

end coherentTopology
