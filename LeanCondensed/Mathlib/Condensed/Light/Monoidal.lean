/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.CartesianClosed
import LeanCondensed.Mathlib.CategoryTheory.Monoidal.Braided.Transport
import LeanCondensed.Mathlib.CategoryTheory.Sites.Monoidal
import LeanCondensed.Mathlib.Condensed.Light.Small
import LeanCondensed.Projects.SheafMonoidal
import LeanCondensed.Projects.MonoidalLinear

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

section

namespace CategoryTheory.MonoidalClosed -- TODO: move

instance {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed

variable {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalCategory E] (F : Transported e ⥤ E)
    (G : E ⥤ Transported e)

def CategoryTheory.Equivalence.monoidalOfComp [(e.functor ⋙ F).Monoidal] : F.Monoidal :=
  monoidalTransport (e.invFunIdAssoc F)

def CategoryTheory.Equivalence.monoidalOfComp' [(G ⋙ e.inverse).Monoidal] : G.Monoidal :=
  letI : (G ⋙ (equivalenceTransported e).inverse ⋙ (equivalenceTransported e).functor).Monoidal :=
    inferInstanceAs
      ((G ⋙ (equivalenceTransported e).inverse) ⋙ (equivalenceTransported e).functor).Monoidal
  monoidalTransport (isoWhiskerLeft G e.counitIso ≪≫ G.rightUnitor)

end

namespace CategoryTheory.Sheaf

variable {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C}
    {A : Type*} [Category A]
    {F G : D ⥤ Sheaf J A} (i : F ⋙ sheafToPresheaf _ _ ≅ G ⋙ sheafToPresheaf _ _)

def natIsoCancel : F ≅ G :=
  NatIso.ofComponents (fun X ↦ (sheafToPresheaf _ _).preimageIso (i.app _)) (by
    intro X Y f
    apply (sheafToPresheaf _ _).map_injective
    simpa [-sheafToPresheaf_map, -sheafToPresheaf_obj] using i.hom.naturality _)

end CategoryTheory.Sheaf

namespace LightCondensed

variable (R : Type u) [CommRing R]

attribute [local instance] monoidalCategory in
instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod.{u} R))

attribute [local instance] monoidalCategory symmetricCategory in
instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

attribute [local instance] monoidalCategory in
def monoidalClosedSmallSheaves : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

attribute [local instance] monoidalCategory monoidalClosedSmallSheaves in
instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

-- Required to get sheafification.
-- TODO: add a global instance for sheafification of type-valued sheaves
attribute [local instance] Types.instConcreteCategory

attribute [local instance] monoidalCategory in
def monoidalOfPostcomp {E : Type*} [Category E] [MonoidalCategory E] (F : E ⥤ LightCondMod.{u} R)
    [(F ⋙ (equivSmall _).functor).Monoidal] : F.Monoidal :=
  letI : (F ⋙ (equivSmall _).symm.inverse).Monoidal :=
    inferInstanceAs (F ⋙ (equivSmall _).functor).Monoidal
  (equivSmall (ModuleCat R)).symm.monoidalOfComp' F


def monoidalOfPrecomp {E : Type*} [Category E] [MonoidalCategory E] (F : LightCondSet.{u} ⥤ E)
    [((equivSmall _).inverse ⋙ F).Monoidal] : F.Monoidal :=
  letI : ((equivSmall _).symm.functor ⋙ F).Monoidal :=
    inferInstanceAs ((equivSmall _).inverse ⋙ F).Monoidal
  letI : (equivSmall (Type u)).symm.inverse.Monoidal :=
    ((Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts
      (equivSmall (Type u)).symm.inverse).mpr inferInstance).some
  monoidalTransport ((equivSmall _).symm.invFunIdAssoc F)

instance : (free R).Monoidal := by
  letI : MonoidalCategory (Sheaf
      ((equivSmallModel _).inverse.inducedTopology (coherentTopology LightProfinite.{u}))
      (ModuleCat.{u} R)) := monoidalCategory _ _
  apply (config := {allowSynthFailures := true}) monoidalOfPostcomp
  apply (config := {allowSynthFailures := true}) monoidalOfPrecomp
  let i : (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (ModuleCat R)).functor ≅
      Sheaf.composeAndSheafify _ (ModuleCat.free R) := by
    refine natIsoCancel ?_
    let j := (((equivSmallModel LightProfinite.{u}).transportSheafificationAdjunction
            (coherentTopology LightProfinite.{u})
            ((equivSmallModel _).inverse.inducedTopology (coherentTopology LightProfinite.{u}))
            (ModuleCat.{u} R)).leftAdjointUniq
            (sheafificationAdjunction (coherentTopology LightProfinite.{u}) _)).symm
    calc _ ≅ ((equivSmall (Type u)).inverse ⋙ (sheafToPresheaf (coherentTopology LightProfinite.{u}) (Type u) ⋙
          (whiskeringRight LightProfinite.{u}ᵒᵖ (Type u) (ModuleCat.{u} R)).obj (ModuleCat.free R) ⋙
            (Equivalence.transportAndSheafify (coherentTopology LightProfinite)
              ((equivSmallModel LightProfinite).inverse.inducedTopology (coherentTopology LightProfinite))
              (equivSmallModel LightProfinite) (ModuleCat R))) ⋙
              (equivSmall (ModuleCat.{u} R)).functor) ⋙
                sheafToPresheaf ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                  (coherentTopology LightProfinite.{u})) (ModuleCat.{u} R) := ?_
      _ ≅ _ := ?_
    · exact isoWhiskerRight (isoWhiskerLeft _ (isoWhiskerRight (isoWhiskerLeft _
        (isoWhiskerLeft _ j)) _)) _
    · refine Functor.associator _ _ _ ≪≫ ?_
      refine isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ ?_
      refine isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _))) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (isoWhiskerLeft _
        (isoWhiskerLeft _ (Functor.associator _ _ _)))) ≪≫ ?_
      refine ?_ ≪≫ (Functor.associator _ _ _).symm
      refine ?_ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm
      refine isoWhiskerLeft (equivSmall (Type u)).inverse
        (isoWhiskerLeft (sheafToPresheaf (coherentTopology LightProfinite) (Type u)) (isoWhiskerLeft
          ((whiskeringRight LightProfiniteᵒᵖ (Type u) (ModuleCat R)).obj (ModuleCat.free R))
            (isoWhiskerLeft (equivSmallModel LightProfinite).op.congrLeft.functor
              (isoWhiskerLeft (H := sheafToPresheaf
                ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                  (coherentTopology LightProfinite.{u})) (ModuleCat.{u} R)) (presheafToSheaf
                    ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                      (coherentTopology LightProfinite.{u}))
                        (ModuleCat.{u} R)) ?_)))) ≪≫ ?_
      · refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · exact isoWhiskerRight (equivSmallModel LightProfinite.{u}).op.counitIso X.val ≪≫
              Functor.leftUnitor _
        · intros
          ext
          simp [equivSmall, Equivalence.sheafCongr,
            Equivalence.sheafCongr.functor, Equivalence.sheafCongr.inverse]
      · refine ?_ ≪≫ (Functor.associator _ _ _)
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine isoWhiskerRight ?_ _
        refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
            (isoWhiskerRight (equivSmallModel LightProfinite.{u}).op.counitIso X.val ≪≫
              Functor.leftUnitor _) (ModuleCat.free R)
        · intros
          apply NatTrans.ext
          apply funext
          intro
          simp only [Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
            Equivalence.sheafCongr.inverse, Equivalence.congrLeft_functor, Equivalence.op_inverse,
            Functor.comp_obj, sheafToPresheaf_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
            Functor.op_obj, Functor.comp_map, sheafToPresheaf_map, whiskeringRight_obj_map,
            whiskeringLeft_obj_map, Equivalence.op_functor, Equivalence.op_counitIso,
            isoWhiskerRight_trans, isoWhiskerRight_twice, Iso.trans_assoc, Iso.trans_hom,
            Iso.symm_hom, isoWhiskerRight_hom, NatIso.op_inv, NatTrans.comp_app,
            CategoryTheory.whiskerLeft_app, CategoryTheory.whiskerRight_app,
            Functor.associator_inv_app, Functor.associator_hom_app, Functor.id_obj, NatTrans.op_app,
            Functor.leftUnitor_hom_app, CategoryTheory.Functor.map_id, Category.comp_id,
            Category.id_comp, Category.assoc]
          simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  exact monoidalTransport i.symm

attribute [local instance] monoidalCategory in
instance : (equivSmall (ModuleCat R)).functor.Monoidal :=
  inferInstanceAs (equivalenceTransported (equivSmall (ModuleCat R)).symm).inverse.Monoidal

attribute [local instance] monoidalCategory in
instance : (equivSmall (ModuleCat R)).inverse.Monoidal := by
  exact (equivSmall (ModuleCat R)).inverseMonoidal

instance : (equivSmall (ModuleCat R)).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance : (equivSmall (ModuleCat R)).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] monoidalCategory CategoryTheory.Sheaf.monoidalPreadditive in
instance : MonoidalPreadditive (LightCondMod.{u} R) := by
  apply monoidalPreadditive_of_faithful (equivSmall (ModuleCat R)).functor

end LightCondensed
