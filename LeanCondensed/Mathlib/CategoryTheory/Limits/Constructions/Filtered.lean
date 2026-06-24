/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Preservation of coproducts from finite coproducts and filtered colimits

This file adds a preservation counterpart to mathlib's construction of coproducts from finite
coproducts and filtered colimits.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits.CoproductsFromFiniteFiltered

universe w v u v' u'

namespace CategoryTheory.Limits

namespace CoproductsFromFiniteFiltered

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-subcoproduct diagram commutes with a functor preserving finite coproducts. -/
noncomputable def liftToFinsetObjCompIso [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G] {α : Type w} (F : Discrete α ⥤ C) :
    liftToFinsetObj F ⋙ G ≅ liftToFinsetObj (F ⋙ G) := by
  refine NatIso.ofComponents (fun S => PreservesCoproduct.iso G (fun x : S => F.obj x)) ?_
  intro S T h
  apply (isColimitOfHasCoproductOfPreservesColimit G (fun x : S => F.obj x)).hom_ext
  intro x
  change G.map (Sigma.ι (fun x : S => F.obj x) x.as) ≫
      G.map (Sigma.desc fun y : S => Sigma.ι (fun x : T => F.obj x) ⟨y, h.down.down y.2⟩) ≫
        (PreservesCoproduct.iso G (fun x : T => F.obj x)).hom =
    G.map (Sigma.ι (fun x : S => F.obj x) x.as) ≫
      (PreservesCoproduct.iso G (fun x : S => F.obj x)).hom ≫
        Sigma.desc (fun y : S => Sigma.ι (fun x : T => G.obj (F.obj x)) ⟨y, h.down.down y.2⟩)
  rw [← G.map_comp_assoc]
  rw [colimit.ι_desc]
  simp only [Cofan.mk_ι_app]
  have hT : G.map (Sigma.ι (fun x : T => F.obj x) ⟨x.as, h.down.down x.as.2⟩) ≫
      (PreservesCoproduct.iso G (fun x : T => F.obj x)).hom =
        Sigma.ι (fun x : T => G.obj (F.obj x)) ⟨x.as, h.down.down x.as.2⟩ := by
    simpa [← PreservesCoproduct.inv_hom] using
      (map_ι_comp_inv_sigmaComparison (G := G) (f := fun x : T => F.obj x)
        ⟨x.as, h.down.down x.as.2⟩)
  rw [hT]
  have hS : G.map (Sigma.ι (fun x : S => F.obj x) x.as) ≫
      (PreservesCoproduct.iso G (fun x : S => F.obj x)).hom =
        Sigma.ι (fun x : S => G.obj (F.obj x)) x.as := by
    simpa [← PreservesCoproduct.inv_hom] using
      (map_ι_comp_inv_sigmaComparison (G := G) (f := fun x : S => F.obj x) x.as)
  rw [← Category.assoc, hS]
  rw [colimit.ι_desc]
  simp only [Cofan.mk_ι_app]

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving finite coproducts and filtered colimits preserves coproducts. -/
lemma preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts_and_filteredColimits
    [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [HasFiniteCoproducts D] [HasFilteredColimitsOfSize.{w, w} D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G]
    [PreservesFilteredColimitsOfSize.{w, w} G] (α : Type w) :
    PreservesColimitsOfShape (Discrete α) G := by
  letI : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  letI : HasCoproducts.{w} D := hasCoproducts_of_finite_and_filtered
  constructor
  intro F
  haveI : PreservesColimitsOfShape (Finset (Discrete α)) G :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits (Finset (Discrete α))
  haveI : PreservesColimit (liftToFinsetObj F) G := inferInstance
  have hpost : colimit.post F G =
      ((liftToFinsetColimIso (C := D) (α := α)).app (F ⋙ G)).inv ≫
        (HasColimit.isoOfNatIso (liftToFinsetObjCompIso G F)).inv ≫
          (preservesColimitIso G (liftToFinsetObj F)).inv ≫
            G.map (((liftToFinsetColimIso (C := C) (α := α)).app F).hom) := by
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_post]
    symm
    let s : Finset (Discrete α) := {j}
    let js : s := ⟨j, by simp [s]⟩
    rw [← liftToFinsetColimIso_aux_assoc (F ⋙ G) js]
    change Sigma.ι (fun x : s => G.obj (F.obj x)) js ≫
        colimit.ι (liftToFinsetObj (F ⋙ G)) s ≫
          (colimit.isoColimitCocone (liftToFinsetColimitCocone (F ⋙ G))).inv ≫
            (colimit.isoColimitCocone (liftToFinsetColimitCocone (F ⋙ G))).hom ≫
              (HasColimit.isoOfNatIso (liftToFinsetObjCompIso G F)).inv ≫
                (preservesColimitIso G (liftToFinsetObj F)).inv ≫
                  G.map ((colimit.isoColimitCocone (liftToFinsetColimitCocone F)).inv) =
      G.map (colimit.ι F j)
    simp only [Iso.inv_hom_id_assoc]
    rw [HasColimit.isoOfNatIso_ι_inv_assoc]
    change Sigma.ι (fun x : s => G.obj (F.obj x)) js ≫
        (PreservesCoproduct.iso G (fun x : s => F.obj x)).inv ≫
          colimit.ι (liftToFinsetObj F ⋙ G) s ≫
            (preservesColimitIso G (liftToFinsetObj F)).inv ≫
              G.map (((liftToFinsetColimIso (C := C) (α := α)).app F).hom) =
      G.map (colimit.ι F j)
    rw [PreservesCoproduct.inv_hom]
    rw [ι_comp_sigmaComparison_assoc]
    rw [ι_preservesColimitIso_inv_assoc]
    rw [← G.map_comp_assoc]
    rw [← G.map_comp]
    apply congrArg G.map
    dsimp [liftToFinsetColimIso]
    simpa [Category.assoc] using liftToFinsetColimIso_aux F js
  haveI : IsIso (colimit.post F G) := by
    rw [hpost]
    infer_instance
  exact preservesColimit_of_isIso_post G F

end CategoryTheory.Limits
