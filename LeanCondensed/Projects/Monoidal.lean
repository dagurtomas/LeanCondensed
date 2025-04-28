/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection

universe u v

noncomputable section

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory
  MonoidalClosed Functor Enriched

attribute [local instance] CategoryTheory.HasForget.instFunLike
  ModuleCat.instMonoidalClosed Sheaf.monoidalCategory

variable (R : Type u) [CommRing R] -- might need some more assumptions

def WalkingMulticospan.map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :
    WalkingMulticospan (multicospanShapeEnd C) ⥤ WalkingMulticospan (multicospanShapeEnd D) :=
  MulticospanIndex.multicospan {
    left := WalkingMulticospan.left ∘ F.obj
    right := WalkingMulticospan.right ∘ F.mapArrow.obj
    fst b :=
      let b' : (multicospanShapeEnd D).R := F.mapArrow.obj b
      WalkingMulticospan.Hom.fst b'
    snd b :=
      let b' : (multicospanShapeEnd D).R := F.mapArrow.obj b
      WalkingMulticospan.Hom.snd b' }

def CategoryTheory.Limits.MulticospanIndex.map {C D E : Type*} [Category C] [Category D] [Category E]
    (I : MulticospanIndex (multicospanShapeEnd D) E)
    (F : C ⥤ D)  : MulticospanIndex (multicospanShapeEnd C) E where
  left := I.left ∘ F.obj
  right := I.right ∘ F.mapArrow.obj
  fst b := I.fst (F.mapArrow.obj b)
  snd b := I.snd (F.mapArrow.obj b)

def multicospanIndexEndCongr {C I J : Type*} [Category C] [Category I] [Category J]
    (i : I ≌ J) (F : Jᵒᵖ ⥤ J ⥤ C) (G : Iᵒᵖ ⥤ I ⥤ C) :
    ((multicospanIndexEnd F).map i.functor).multicospan ≅ (multicospanIndexEnd G).multicospan := by
  refine NatIso.ofComponents ?_ ?_
  · rintro (X | X)
    · dsimp [MulticospanIndex.map, WalkingMulticospan.map, multicospanIndexEnd]
      let j : Iᵒᵖ ⥤ I ⥤ C ≌ Jᵒᵖ ⥤ J ⥤ C := (i.congrLeft (E := C)).congrRight.trans i.op.congrLeft
      change ((j.inverse.obj F).obj _).obj _ ≅ _
      let e : j.inverse.obj F ≅ G := by
        refine NatIso.ofComponents ?_ ?_
        · intro X
          simp [j]
          refine NatIso.ofComponents ?_ ?_
          · intro Y
            simp [j]
            sorry
          · sorry
        · sorry
      exact (e.app _).app _
    · dsimp [MulticospanIndex.map, WalkingMulticospan.map, multicospanIndexEnd]
      sorry
  · rintro X Y (f | f | f)
    · simp
    · sorry
    · sorry

lemma WalkingMulticospan.comp_map {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (I : MulticospanIndex (multicospanShapeEnd D) E) :
      WalkingMulticospan.map F ⋙ I.multicospan = (I.map F).multicospan := by
  fapply CategoryTheory.Functor.ext
  · rintro (X | X)
    all_goals simp [MulticospanIndex.map, map]
  · rintro X Y (f | f | f)
    all_goals simp [MulticospanIndex.map, map]

-- instance {C D : Type*} [Category C] [Category D] (F : C ⥤ D) [F.IsEquivalence] :
--     (WalkingMulticospan.map F).Initial where
--   out := by
--     rintro (X | X)
--     · sorry
--     · sorry

lemma WalkingMulticospan.eqOfIso (J : MulticospanShape) (X Y : J.L) (f g : J.R)
    (hf₁ : J.fst f = X) (hf₂ : J.snd f = Y) (hg₁ : J.fst g = Y) (hg₂ : J.snd g = X) :
    WalkingMulticospan.left X = WalkingMulticospan.left Y := by
  sorry

def walkingMulticospanEquivalence {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) :
    WalkingMulticospan (multicospanShapeEnd C) ≌
      WalkingMulticospan (multicospanShapeEnd D) where
  functor := MulticospanIndex.multicospan {
    left := WalkingMulticospan.left ∘ e.functor.obj
    right := WalkingMulticospan.right ∘ e.functor.mapArrow.obj
    fst b :=
      let b' : (multicospanShapeEnd D).R := e.functor.mapArrow.obj b
      WalkingMulticospan.Hom.fst b'
    snd b :=
      let b' : (multicospanShapeEnd D).R := e.functor.mapArrow.obj b
      WalkingMulticospan.Hom.snd b' }
  inverse := MulticospanIndex.multicospan {
    left := WalkingMulticospan.left ∘ e.inverse.obj
    right := WalkingMulticospan.right ∘ e.inverse.mapArrow.obj
    fst b :=
      let b' : (multicospanShapeEnd C).R := e.inverse.mapArrow.obj b
      WalkingMulticospan.Hom.fst b'
    snd b :=
      let b' : (multicospanShapeEnd C).R := e.inverse.mapArrow.obj b
      WalkingMulticospan.Hom.snd b' }
  unitIso := by
    refine NatIso.ofComponents ?_ ?_
    · rintro (X | X)
      · refine eqToIso ?_
        simp only [id_obj, multicospanShapeEnd_L, multicospanShapeEnd_R, mapArrow_obj, comp_obj,
          MulticospanIndex.multicospan_obj, Function.comp_apply]
        sorry
      · refine eqToIso ?_
        sorry
      -- · simp
      --   exact {
      --     hom := sorry
      --     inv := sorry
      --     hom_inv_id := sorry
      --     inv_hom_id := sorry
      --   }
      -- · simp
      --   sorry
    · sorry
  counitIso := by
    refine NatIso.ofComponents ?_ ?_
    · rintro (X | X)
      · simp
        exact {
          hom := sorry
          inv := sorry
          hom_inv_id := sorry
          inv_hom_id := sorry
        }
      · sorry
    · sorry
  functor_unitIso_comp := sorry

instance {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C] :
    EssentiallySmall.{u} (WalkingMulticospan (multicospanShapeEnd C)) where
  equiv_smallCategory :=
    ⟨WalkingMulticospan (multicospanShapeEnd (SmallModel C)), inferInstance,
      ⟨walkingMulticospanEquivalence (equivSmallModel C)⟩⟩

instance {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C] (X : C) :
    EssentiallySmall.{u} (Under X) :=
  sorry

instance : HasLimitsOfShape
    (WalkingMulticospan (multicospanShapeEnd LightProfinite.{u}ᵒᵖ)) (ModuleCat.{u} R) :=
  hasLimitsOfShape_of_essentiallySmall _ _

instance (S : LightProfinite.{u}ᵒᵖ) :
    HasLimitsOfShape (WalkingMulticospan (multicospanShapeEnd (Under S))) (ModuleCat.{u} R) :=
  hasLimitsOfShape_of_essentiallySmall _ _

instance : ((coherentTopology LightProfinite.{u}).W (A := ModuleCat R)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/- This is the monoidal structure on localized categories. -/
instance : MonoidalCategory (LightCondMod.{u} R) := CategoryTheory.Sheaf.monoidalCategory _ _

instance : MonoidalClosed (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R) :=
  FunctorCategory.monoidalClosed

/- Constructed using Day's reflection theorem. -/
instance : MonoidalClosed (LightCondMod.{u} R) :=
  haveI : HasWeakSheafify ((coherentTopology LightProfinite.{u})) (ModuleCat R) :=
    inferInstance
  haveI : (presheafToSheaf (coherentTopology LightProfinite) (ModuleCat R)).Monoidal :=
    inferInstance
  haveI : (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Faithful :=
    (fullyFaithfulSheafToPresheaf _ _).faithful
  haveI :  (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat R)).Full :=
    (fullyFaithfulSheafToPresheaf _ _).full
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalPreadditive (LightCondMod.{u} R) := sorry

instance : SymmetricCategory (LightCondMod.{u} R) := sorry
