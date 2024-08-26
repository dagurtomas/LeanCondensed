/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.ModuleCat.Basic

open CategoryTheory

variable {C : Type*} [Category C]
variable (J : GrothendieckTopology C)
variable {A : Type*} [Category A]
variable {B : Type*} [Category B]
variable (s : A ⥤ B) [s.Faithful]
variable {F G : Sheaf J A} (α : F.val ⋙ s ⟶ G.val ⋙ s) (h : ∀ X, ∃ f, α.app X = s.map f)

noncomputable
def presheafForgetPromote : F.val ⟶ G.val where
  app X := (h X).choose
  naturality X Y f := by
    have := α.naturality f
    rw [(h Y).choose_spec, (h X).choose_spec] at this
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp] at this
    exact s.map_injective this

noncomputable
def sheafForgetPromote : F ⟶ G := ⟨presheafForgetPromote J s α h⟩

variable [J.HasSheafCompose s]

lemma map_sheafForgetPromote :
    ((sheafCompose J s).map (sheafForgetPromote J s α h)).val = α := by
  ext
  simp only [sheafCompose, Functor.comp_obj, sheafForgetPromote, presheafForgetPromote,
    whiskerRight_app, ← (h _).choose_spec]

variable {H I : Sheaf J A} (β : H.val ⋙ s ⟶ I.val ⋙ s)
    (hβ : ∀ X, ∃ f, β.app X = s.map f) (f : F ⟶ H) (g : G ⟶ I)
    (w : ((sheafCompose J s).map f).val ≫ β = α ≫ ((sheafCompose J s).map g).val)

instance : (sheafCompose J s ⋙ sheafToPresheaf _ _).Faithful :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj s).Faithful from inferInstance

instance : (sheafCompose J s).Faithful :=
  Functor.Faithful.of_comp (sheafCompose J s) (sheafToPresheaf _ _)

include w in
lemma naturality_promote : f ≫ sheafForgetPromote _ _ β hβ =
    sheafForgetPromote _ _ α h ≫ g := by
  apply (sheafCompose J s).map_injective
  apply Sheaf.hom_ext
  simpa only [Functor.map_comp, Sheaf.instCategorySheaf_comp_val, map_sheafForgetPromote]

instance [s.ReflectsIsomorphisms] : (sheafCompose J s).ReflectsIsomorphisms where
  reflects f h := by
    have : IsIso ((sheafCompose J s).map f).val :=
      (inferInstance : IsIso ((sheafToPresheaf _ _).mapIso (asIso ((sheafCompose J s).map f))).hom)
    rw [@sheafCompose_map_val] at this
    apply (config := { allowSynthFailures := true }) isIso_of_fully_faithful (sheafToPresheaf _ _)
    apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
    intro X
    have := NatIso.isIso_app_of_isIso (whiskerRight f.val s) X
    simp only [Functor.comp_obj, whiskerRight_app] at this
    exact Functor.ReflectsIsomorphisms.reflects s (f.val.app X)
