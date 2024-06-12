/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Module
import Mathlib.Algebra.Category.ModuleCat.Limits

universe u w

open CategoryTheory

section Presheaves

variable {C : Type*} [Category C]

variable (R : Type w) [Ring R]

variable {F : C ⥤ Type w} [∀ (X : C), AddCommGroup (F.obj X)] [∀ (X : C), Module R (F.obj X)]

namespace CategoryTheory.Functor

variable (F) in
structure IsPromotable : Type _ where
  isLinearMap {X Y : C} (f : X ⟶ Y) : IsLinearMap R (F.map f)

variable (hF : IsPromotable R F)

def promote : C ⥤ ModuleCat.{w} R where
  obj X := ModuleCat.of R (F.obj X)
  map f := ModuleCat.asHom {
    toFun := F.map f
    map_add' := (hF.isLinearMap f).map_add
    map_smul' := (hF.isLinearMap f).map_smul }

variable {G : C ⥤ Type w} [∀ (X : C), AddCommGroup (G.obj X)] [∀ (X : C), Module R (G.obj X)]

variable (hG : IsPromotable R G)

variable {α : F ⟶ G} (h : ∀ X : C, IsLinearMap R (α.app X))

def promoteMap : promote R hF ⟶ promote R hG where
  app X := ModuleCat.asHom {
    toFun := α.app X
    map_add' := (h X).map_add
    map_smul' := (h X).map_smul }
  naturality X Y g := by
    ext
    change (F.map _ ≫ α.app _) _ = _
    rw [α.naturality]
    rfl

variable {H : Type u ⥤ (C ⥤ Type w)}
  [∀ (X : Type _) [AddCommGroup X] [Module R X] (Y : C), AddCommGroup ((H.obj X).obj Y)]
  [∀ (X : Type _) [AddCommGroup X] [Module R X] (Y : C), Module R ((H.obj X).obj Y)]

variable (H) in
structure IsPromotableFunctor : Type _ where
  isLinearMapMap {Z : Type _} [AddCommGroup Z] [Module R Z] {X Y : C} (f : X ⟶ Y) :
      IsLinearMap R ((H.obj Z).map f)
  isLinearMapApp {X Y : Type _} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
      {Z : C} (f : X ⟶ Y) :
      IsLinearMap R ((H.map f).app Z)


/-
failed to synthesize instance
  (X : Type u) → [inst : AddCommGroup X] → [inst : Module R X] → (Y : C) → AddCommGroup ((H.obj X).obj Y)
-/
-- variable (HH : IsPromotableFunctor R H)

end Functor

end CategoryTheory

end Presheaves

namespace Condensed

variable (R : Type (u+1)) [Ring R]
variable {X : CondensedSet.{u}} [∀ (S : CompHaus), AddCommGroup (X.val.obj ⟨S⟩)]
  [∀ (S : CompHaus), Module R (X.val.obj ⟨S⟩)]
  (h : ∀ (S T : CompHaus) (f : T ⟶ S),
    IsLinearMap R (X.val.map f.op))

variable (X) in
@[simps]
def promote : CondensedMod.{u} R where
  val := {
    obj := fun S ↦ ModuleCat.of R (X.val.obj S)
    map := fun f ↦ ModuleCat.asHom {
      toFun := X.val.map f
      map_add' := (h _ _ f.unop).map_add
      map_smul' := (h _ _ f.unop).map_smul } }
  cond := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget _)]
    exact X.cond

variable {Y : CondensedSet.{u}}
  [∀ (S : CompHaus), AddCommGroup (Y.val.obj ⟨S⟩)]
  [∀ (S : CompHaus), Module R (Y.val.obj ⟨S⟩)] (hY : ∀ (S T : CompHaus) (f : T ⟶ S),
    IsLinearMap R (Y.val.map f.op))
  (f : X ⟶ Y)
  (hh : ∀ S : CompHaus, IsLinearMap R (f.val.app ⟨S⟩))

def promoteMap : promote R X h ⟶ promote R Y hY where
  val := {
    app := fun S ↦ ModuleCat.asHom {
      toFun := f.val.app S
      map_add' := (hh _).map_add
      map_smul' := (hh _).map_smul }
    naturality := by
      intros
      ext
      change (X.val.map _ ≫ f.val.app _) _ = _
      rw [f.val.naturality]
      rfl }

lemma isLinearMap_id (S : CompHaus) : IsLinearMap R ((𝟙 X : Sheaf.Hom _ _).val.app ⟨S⟩) := sorry

lemma promoteMap_id : promoteMap R h h (𝟙 X) (isLinearMap_id R) = 𝟙 _ := rfl

variable (F : Type (u+1) ⥤ CondensedSet.{u})
  [∀ (X : Type _) [AddCommGroup X] [Module R X]
    (S : CompHaus), AddCommGroup ((F.obj X).val.obj ⟨S⟩)]
  [∀ (X : Type _) [AddCommGroup X] [Module R X] (S : CompHaus),
    Module R ((F.obj X).val.obj ⟨S⟩)]
  (h : ∀ (X : Type _) [AddCommGroup X] [Module R X] (S T : CompHaus) (f : T ⟶ S),
    IsLinearMap R ((F.obj X).val.map f.op))
  (hh : ∀ (X Y : Type _) [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (S : CompHaus), IsLinearMap R ((F.map f.toFun).val.app ⟨S⟩))

def promoteFunctor : ModuleCat.{u+1} R ⥤ CondensedMod.{u} R where
  obj X := promote R (F.obj X.1) (h X.1)
  map f := promoteMap R _ _ (F.map f) (hh _ _ f)
  map_id X := by
    simp
    apply Sheaf.hom_ext
    ext1
    sorry

  map_comp := sorry
