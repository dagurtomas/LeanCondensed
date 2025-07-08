/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Combinatorics.Quiver.ReflQuiver

universe v u

open CategoryTheory MonoidalCategory Sheaf Functor.Monoidal Category

namespace CategoryTheory.Functor.Monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]

@[reassoc]
lemma map_whiskerLeft' (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.obj X ◁ F.map f = μ F X Y ≫ F.map (X ◁ f) ≫ δ F X Z := by
  rw [map_whiskerLeft]
  simp [-μ_natural_right, -δ_natural_right_assoc, -δ_natural_right]

@[reassoc]
lemma map_whiskerRight' {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map f ▷ F.obj Z = μ F X Z ≫ F.map (f ▷ Z) ≫ δ F Y Z := by
  rw [map_whiskerRight]
  simp [-μ_natural_left, -δ_natural_left_assoc, -δ_natural_left]

end CategoryTheory.Functor.Monoidal

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable [Preadditive C] [MonoidalPreadditive C] [Preadditive D]

instance : Preadditive (LocalizedMonoidal L W ε) := inferInstanceAs (Preadditive D)

instance [L.Additive] : (L').Additive := inferInstanceAs (L.Additive)

def monoidalPreadditive [L.Additive] (R : D ⥤ C) [R.Full] [R.Faithful] (adj : L ⊣ R) :
    MonoidalPreadditive (LocalizedMonoidal L W ε) where
  whiskerLeft_zero {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (L').obj X' ◁ (0 : (L').obj Y' ⟶ (L').obj Z') = 0 by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero, map_whiskerLeft']
    simp
  zero_whiskerRight {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (0 : (L').obj Y' ⟶ (L').obj Z') ▷ (L').obj X' = 0 by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero, map_whiskerRight']
    simp
  whiskerLeft_add {X Y Z} f g := by
    let eX : (L').obj (R.obj X) ≅ X := asIso (adj.counit.app X)
    let eY : (L').obj (R.obj Y) ≅ Y := asIso (adj.counit.app Y)
    let eZ : (L').obj (R.obj Z) ≅ Z := asIso (adj.counit.app Z)
    suffices (L').obj (R.obj X) ◁ ((L').map (R.map f) + (L').map (R.map g)) =
        ((L').obj (R.obj X) ◁ (L').map (R.map f)) + ((L').obj (R.obj X) ◁ (L').map (R.map g)) by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp_assoc, ← Functor.map_add, ← tensor_comp]
        simp [eZ, eY]
      · rw [← id_tensorHom, ← id_tensorHom, ← id_tensorHom,
          CategoryTheory.Preadditive.comp_add_assoc, ← tensor_comp, ← tensor_comp,
          CategoryTheory.Preadditive.add_comp, ← tensor_comp, ← tensor_comp]
        simp [eY, eZ]
    rw [← Functor.map_add, map_whiskerLeft', map_whiskerLeft', map_whiskerLeft' (F := L')]
    simp
  add_whiskerRight {X Y Z} f g := by
    let eX : (L').obj (R.obj X) ≅ X := asIso (adj.counit.app X)
    let eY : (L').obj (R.obj Y) ≅ Y := asIso (adj.counit.app Y)
    let eZ : (L').obj (R.obj Z) ≅ Z := asIso (adj.counit.app Z)
    suffices  ((L').map (R.map f) + (L').map (R.map g)) ▷ (L').obj (R.obj X) =
        ((L').map (R.map f)) ▷ (L').obj (R.obj X) + ((L').map (R.map g) ▷ (L').obj (R.obj X)) by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp_assoc, ← Functor.map_add, ← tensor_comp]
        simp [eZ, eY]
      · rw [← tensorHom_id, ← tensorHom_id, ← tensorHom_id,
          CategoryTheory.Preadditive.comp_add_assoc, ← tensor_comp, ← tensor_comp,
          CategoryTheory.Preadditive.add_comp, ← tensor_comp, ← tensor_comp]
        simp [eY, eZ]
    rw [← Functor.map_add, map_whiskerRight', map_whiskerRight', map_whiskerRight' (F := L')]
    simp

def monoidalLinear (A : Type u) [Ring A] [L.Additive] (R : D ⥤ C) [R.Full] [R.Faithful]
    (adj : L ⊣ R) [Linear A D] [Linear A C] [L.Linear A]
    [MonoidalLinear A C] :
    @MonoidalLinear A _ (LocalizedMonoidal L W ε) _ _ (inferInstanceAs (Linear A D)) _
      (monoidalPreadditive L W ε R adj) := by
  haveI := monoidalPreadditive L W ε R adj
  letI : Linear A (LocalizedMonoidal L W ε) := inferInstanceAs (Linear A D)
  letI : (L').Linear A := inferInstanceAs (L.Linear A)
  refine ⟨?_, ?_⟩
  · intro X Y Z r f
    let eX : (L').obj (R.obj X) ≅ X := asIso (adj.counit.app X)
    let eY : (L').obj (R.obj Y) ≅ Y := asIso (adj.counit.app Y)
    let eZ : (L').obj (R.obj Z) ≅ Z := asIso (adj.counit.app Z)
    suffices ((L').obj (R.obj X)) ◁ (r • (L').map (R.map f)) =
        r • ((L').obj (R.obj X)) ◁ ((L').map (R.map f)) by
      refine Eq.trans ?_ (((eX.inv ⊗ₘ eY.inv) ≫= this =≫ (eX.hom ⊗ₘ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp_assoc, ← Functor.map_smul, ← tensor_comp]
        simp [eZ, eY]
      · simp [eX, eY, eZ, ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensor_comp]
    rw [← Functor.map_smul, map_whiskerLeft', map_whiskerLeft']
    simp
  · intro r Y Z f X
    let eX : (L').obj (R.obj X) ≅ X := asIso (adj.counit.app X)
    let eY : (L').obj (R.obj Y) ≅ Y := asIso (adj.counit.app Y)
    let eZ : (L').obj (R.obj Z) ≅ Z := asIso (adj.counit.app Z)
    suffices (r • (L').map (R.map f)) ▷ ((L').obj (R.obj X)) =
        r • ((L').map (R.map f)) ▷ ((L').obj (R.obj X)) by
      refine Eq.trans ?_ (((eY.inv ⊗ₘ eX.inv) ≫= this =≫ (eZ.hom ⊗ₘ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp_assoc, ← Functor.map_smul, ← tensor_comp]
        simp [eZ, eY]
      · simp [eX, eY, eZ, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensor_comp]
    rw [← Functor.map_smul, map_whiskerRight', map_whiskerRight']
    simp

end CategoryTheory.Localization.Monoidal

section Preadditive

variable {C : Type*} [Category C]  (J : GrothendieckTopology C) (A : Type*) [Category A]
    [Preadditive A]

def sheafHomAddEquiv (X Y : Sheaf J A) : (X ⟶ Y) ≃+ (X.val ⟶ Y.val) where
  toFun f := f.val
  invFun f := ⟨f⟩
  left_inv := by intro; rfl
  right_inv := by intro; rfl;
  map_add' := by intros; rfl

instance [HasSheafify J A] [Limits.HasBinaryProducts A] : (presheafToSheaf J A).Additive :=
  Functor.additive_of_preserves_binary_products _

section Linear

variable (R : Type u) [Ring R]

instance [Linear R A] : Linear R (Sheaf J A) where
  homModule X Y := (sheafHomAddEquiv J A X Y).module R
  smul_comp X Y Z r f g := by
    have : (r • f.val) ≫ g.val = r • (f.val ≫ g.val) := by simp
    apply hom_ext
    simp only [comp_val]
    exact this
  comp_smul X Y Z f r g := by
    have : f.val ≫ (r • g.val) = r • (f.val ≫ g.val) := by simp
    apply hom_ext
    simp only [comp_val]
    exact this

end Linear

instance [MonoidalCategory A] [MonoidalPreadditive A] : MonoidalPreadditive (C ⥤ A) where

def CategoryTheory.Sheaf.monoidalPreadditive [MonoidalCategory A]
    [(J.W (A := A)).IsMonoidal] [HasSheafify J A] [Limits.HasBinaryProducts A]
    [MonoidalPreadditive A] :
    letI := monoidalCategory J A
    MonoidalPreadditive (Sheaf J A) :=
  Localization.Monoidal.monoidalPreadditive
    (L := presheafToSheaf J A) (W := J.W (A := A)) (Iso.refl _)
    (R := sheafToPresheaf J A) (sheafificationAdjunction J A)

instance [MonoidalCategory A] [MonoidalPreadditive A]
    (R : Type u) [Ring R] [Linear R A] [MonoidalLinear R A] : MonoidalLinear R (C ⥤ A) where

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.monoidalPreadditive in
def CategoryTheory.Sheaf.monoidalLinear [MonoidalCategory A]
    [(J.W (A := A)).IsMonoidal] [HasSheafify J A] [Limits.HasBinaryProducts A]
    [MonoidalPreadditive A] (R : Type u) [Ring R] [Linear R A]
    [MonoidalLinear R A] [(presheafToSheaf J A).Linear R] :
    MonoidalLinear R (Sheaf J A) :=
  Localization.Monoidal.monoidalLinear (A := R)
    (L := presheafToSheaf J A) (W := J.W (A := A)) (Iso.refl _)
    (R := sheafToPresheaf J A) (sheafificationAdjunction J A)

-- TODO: figure out when the sheafification functor is `R`-linear.

end Preadditive
