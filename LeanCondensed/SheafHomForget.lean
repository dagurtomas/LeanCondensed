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
