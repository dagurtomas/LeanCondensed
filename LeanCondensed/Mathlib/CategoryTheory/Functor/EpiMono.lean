import Mathlib

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}

lemma epi_of_Retract {f g : Arrow C} (π : f ⟶ g) [Epi f.hom] [Epi π.right] : Epi g.hom :=
  have : Epi (π.left ≫ g.hom) := by
    rw [←Functor.id_map π.left, π.w, Functor.id_map]
    exact epi_comp f.hom π.right
  epi_of_epi (π.left) _

lemma preservesEpi_of_Epi (f : F ⟶ G) (hf : ∀ X, Epi (f.app X)) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves {X Y} π hπ :=
    have : Epi (f.app X ≫ G.map π) := by
      rw [←f.naturality π]
      exact epi_comp (F.map π) (f.app Y)
    epi_of_epi (f.app X) (G.map π)

lemma preservesEpi_ofRetract (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (preservesEpi_of_Epi _
    (fun _ ↦ (SplitEpi.mk (r.i.app _)
    (by rw [←NatTrans.comp_app, r.retract, NatTrans.id_app])).epi)).preserves
