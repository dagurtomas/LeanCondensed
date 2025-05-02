import Mathlib

universe v u

open CategoryTheory MonoidalCategory Sheaf Functor.Monoidal

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable [Preadditive C] [MonoidalPreadditive C] [Preadditive D]

instance : Preadditive (LocalizedMonoidal L W ε) := inferInstanceAs (Preadditive D)

instance [L.Additive] : (L').Additive := inferInstanceAs (L.Additive)

-- this may need some additional assumptions on the localization.
instance [L.Additive] : MonoidalPreadditive (LocalizedMonoidal L W ε) where
  whiskerLeft_zero {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (L').obj X' ◁ (0 : (L').obj Y' ⟶ (L').obj Z') = 0 by
      refine Eq.trans ?_ (((eX.inv ⊗ eY.inv) ≫= this =≫ (eX.hom ⊗ eZ.hom)).trans ?_)
      · rw [← id_tensorHom, ← id_tensorHom, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero]
    have : (L').obj X' ◁ (L').map (0 : Y' ⟶ Z') =
        Functor.LaxMonoidal.μ (L') _ _ ≫ (L').map (X' ◁ (0 : Y' ⟶ Z')) ≫
          Functor.OplaxMonoidal.δ (L') _ _ := by
      rw [map_whiskerLeft_assoc]
      simp
    rw [this]
    simp
  zero_whiskerRight {X Y Z} := by
    obtain ⟨X', ⟨eX⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ X) := ⟨_, ⟨(L').objObjPreimageIso X⟩⟩
    obtain ⟨Y', ⟨eY⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Y) := ⟨_, ⟨(L').objObjPreimageIso Y⟩⟩
    obtain ⟨Z', ⟨eZ⟩⟩ : ∃ X₁, Nonempty ((L').obj X₁ ≅ Z) := ⟨_, ⟨(L').objObjPreimageIso Z⟩⟩
    suffices (0 : (L').obj Y' ⟶ (L').obj Z') ▷ (L').obj X' = 0 by
      refine Eq.trans ?_ (((eY.inv ⊗ eX.inv) ≫= this =≫ (eZ.hom ⊗ eX.hom)).trans ?_)
      · rw [← tensorHom_id, ← tensorHom_id, ← tensor_comp, ← tensor_comp]
        simp
      · simp
    rw [← Functor.PreservesZeroMorphisms.map_zero]
    have : (L').map (0 : Y' ⟶ Z') ▷ (L').obj X' =
        Functor.LaxMonoidal.μ (L') _ _ ≫ (L').map ((0 : Y' ⟶ Z') ▷ X') ≫
          Functor.OplaxMonoidal.δ (L') _ _ := by
      rw [map_whiskerRight_assoc]
      simp
    rw [this]
    simp
  whiskerLeft_add {X Y Z} f g := by sorry
  add_whiskerRight {X Y Z} f g := sorry

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
    simp only [instCategorySheaf_comp_val]
    exact this
  comp_smul X Y Z f r g := by
    have : f.val ≫ (r • g.val) = r • (f.val ≫ g.val) := by simp
    apply hom_ext
    simp only [instCategorySheaf_comp_val]
    exact this

end Linear

instance [MonoidalCategory A] [MonoidalPreadditive A] : MonoidalPreadditive (C ⥤ A) where

def CategoryTheory.Sheaf.monoidalPreadditive [MonoidalCategory A]
    [(J.W (A := A)).IsMonoidal] [HasSheafify J A] [Limits.HasBinaryProducts A]
    [MonoidalPreadditive A] :
    haveI := monoidalCategory J A
    MonoidalPreadditive (Sheaf J A) :=
  inferInstanceAs (MonoidalPreadditive
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W (A := A)) (Iso.refl _)))

end Preadditive
