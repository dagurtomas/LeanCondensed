/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Two-variable derived functors from concrete replacements

This file packages the localization construction of derived bifunctors using the concrete classes of
complexes which usually compute derived functors:

* K-projective complexes for left-derived bifunctors;
* K-injective complexes for right-derived bifunctors;
* K-flat complexes for monoidal left-derived tensor products.

The construction is intentionally phrased with explicit hypotheses saying that the corresponding
subcategory of replacement complexes computes the derived category.  In applications, those
hypotheses should be proved from enough K-projective/K-injective/K-flat resolutions, rather than
being hidden in an artificial adapted-object abstraction.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Localization

namespace CategoryTheory
namespace DerivedCategory
namespace TwoVariable

universe v₁ v₂ v₃ u₁ u₂ u₃

attribute [local instance] HasDerivedCategory.standard

/-- Cochain complexes indexed by `ℤ`. -/
abbrev Complex (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] := CochainComplex C ℤ

/-- Quasi-isomorphisms of cochain complexes. -/
abbrev W (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    MorphismProperty (Complex C) :=
  HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

section KProjective

/-- The object property of being K-projective. -/
abbrev kProjectiveComplexes (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    ObjectProperty (Complex C) :=
  fun K => CochainComplex.IsKProjective K

/-- The full subcategory of K-projective cochain complexes. -/
abbrev KProjectiveComplex (C : Type u₁) [Category.{v₁} C] [Abelian C] :=
  (kProjectiveComplexes C).FullSubcategory

/-- The inclusion of K-projective complexes. -/
abbrev kProjectiveInclusion (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    KProjectiveComplex C ⥤ Complex C :=
  (kProjectiveComplexes C).ι

/-- Quasi-isomorphisms between K-projective complexes. -/
abbrev kProjectiveQuasiIso (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    MorphismProperty (KProjectiveComplex C) :=
  (W C).inverseImage (kProjectiveInclusion C)

/-- The inclusion of K-projective complexes as a morphism of localizers. -/
def kProjectiveLocalizer (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    LocalizerMorphism (kProjectiveQuasiIso C) (W C) where
  functor := kProjectiveInclusion C
  map _ _ _ hf := hf

/-- A K-projective resolution of a complex `K` is a quasi-isomorphism `P ⟶ K` from a
K-projective complex. -/
def HasKProjectiveResolution {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : Complex C) : Prop :=
  ∃ (P : Complex C), CochainComplex.IsKProjective P ∧ ∃ q : P ⟶ K, W C q

/-- The concrete enough-K-projectives hypothesis: every complex has a K-projective resolution. -/
abbrev HasEnoughKProjectives (C : Type u₁) [Category.{v₁} C] [Abelian C] : Prop :=
  ∀ K : Complex C, HasKProjectiveResolution K

/-- Obligation: an abelian category with enough projective objects has enough K-projective
resolutions of complexes. -/
lemma hasEnoughKProjectives_of_enoughProjectives
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [EnoughProjectives C] :
    HasEnoughKProjectives C := by
  sorry

/-- Obligation: enough K-projective resolutions imply that K-projective complexes compute the
derived category. -/
lemma kProjectiveLocalizer_isLocalizedEquivalence_of_hasEnoughKProjectives
    (C : Type u₁) [Category.{v₁} C] [Abelian C] (hC : HasEnoughKProjectives C) :
    (kProjectiveLocalizer C).IsLocalizedEquivalence := by
  sorry

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
variable [Abelian C₁] [Abelian C₂] [Abelian C₃]

/-- Restrict a bifunctor on complexes to K-projective complexes in both variables. -/
abbrev restrict₂KProjective (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) :
    KProjectiveComplex C₁ × KProjectiveComplex C₂ ⥤ Complex C₃ :=
  ((kProjectiveInclusion C₁).prod (kProjectiveInclusion C₂)) ⋙ Functor.uncurry.obj T

/-- The condition that a bifunctor sends quasi-isomorphisms between K-projective complexes in both
variables to quasi-isomorphisms after localization. -/
abbrev InvertsKProjectiveQuasiIso₂ (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) : Prop :=
  ((kProjectiveQuasiIso C₁).prod (kProjectiveQuasiIso C₂)).IsInvertedBy
    (restrict₂KProjective T ⋙ DerivedCategory.Q)

/-- The functor on the localized categories of K-projective complexes induced by a bifunctor. -/
noncomputable def localized₂ByKProjectives (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKProjectiveQuasiIso₂ T) :
    (kProjectiveQuasiIso C₁).Localization × (kProjectiveQuasiIso C₂).Localization ⥤
      DerivedCategory C₃ :=
  Localization.lift (restrict₂KProjective T ⋙ DerivedCategory.Q) hT
    ((kProjectiveQuasiIso C₁).Q.prod (kProjectiveQuasiIso C₂).Q)

/-- If K-projective complexes compute the derived category, their localized category is equivalent
to the usual derived category. -/
noncomputable def kProjectiveLocalizationEquivalence
    (C : Type u₁) [Category.{v₁} C] [Abelian C] (hC : HasEnoughKProjectives C) :
    (kProjectiveQuasiIso C).Localization ≌ DerivedCategory C := by
  letI : (kProjectiveLocalizer C).IsLocalizedEquivalence :=
    kProjectiveLocalizer_isLocalizedEquivalence_of_hasEnoughKProjectives C hC
  exact ((kProjectiveLocalizer C).localizedFunctor (kProjectiveQuasiIso C).Q
    DerivedCategory.Q).asEquivalence

/-- The two-variable left-derived functor computed by K-projective replacements. -/
noncomputable def leftDerived₂ByKProjectives (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKProjectiveQuasiIso₂ T)
    (hC₁ : HasEnoughKProjectives C₁) (hC₂ : HasEnoughKProjectives C₂) :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  ((kProjectiveLocalizationEquivalence C₁ hC₁).inverse.prod
      (kProjectiveLocalizationEquivalence C₂ hC₂).inverse) ⋙
    localized₂ByKProjectives T hT

/-- Curried form of `leftDerived₂ByKProjectives`. -/
noncomputable def leftDerived₂ByKProjectivesCurried
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKProjectiveQuasiIso₂ T)
    (hC₁ : HasEnoughKProjectives C₁) (hC₂ : HasEnoughKProjectives C₂) :
    DerivedCategory C₁ ⥤ DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  Functor.curry.obj (leftDerived₂ByKProjectives T hT hC₁ hC₂)

end KProjective

section KInjective

/-- The object property of being K-injective. -/
abbrev kInjectiveComplexes (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    ObjectProperty (Complex C) :=
  fun K => CochainComplex.IsKInjective K

/-- The full subcategory of K-injective cochain complexes. -/
abbrev KInjectiveComplex (C : Type u₁) [Category.{v₁} C] [Abelian C] :=
  (kInjectiveComplexes C).FullSubcategory

/-- The inclusion of K-injective complexes. -/
abbrev kInjectiveInclusion (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    KInjectiveComplex C ⥤ Complex C :=
  (kInjectiveComplexes C).ι

/-- Quasi-isomorphisms between K-injective complexes. -/
abbrev kInjectiveQuasiIso (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    MorphismProperty (KInjectiveComplex C) :=
  (W C).inverseImage (kInjectiveInclusion C)

/-- The inclusion of K-injective complexes as a morphism of localizers. -/
def kInjectiveLocalizer (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    LocalizerMorphism (kInjectiveQuasiIso C) (W C) where
  functor := kInjectiveInclusion C
  map _ _ _ hf := hf

/-- A K-injective resolution of a complex `K` is a quasi-isomorphism `K ⟶ I` to a
K-injective complex. -/
def HasKInjectiveResolution {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (K : Complex C) : Prop :=
  ∃ (I : Complex C), CochainComplex.IsKInjective I ∧ ∃ q : K ⟶ I, W C q

/-- The concrete enough-K-injectives hypothesis: every complex has a K-injective resolution. -/
abbrev HasEnoughKInjectives (C : Type u₁) [Category.{v₁} C] [Abelian C] : Prop :=
  ∀ K : Complex C, HasKInjectiveResolution K

/-- Obligation: an abelian category with enough injective objects has enough K-injective
resolutions of complexes. -/
lemma hasEnoughKInjectives_of_enoughInjectives
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [EnoughInjectives C] :
    HasEnoughKInjectives C := by
  sorry

/-- Obligation: enough K-injective resolutions imply that K-injective complexes compute the
derived category. -/
lemma kInjectiveLocalizer_isLocalizedEquivalence_of_hasEnoughKInjectives
    (C : Type u₁) [Category.{v₁} C] [Abelian C] (hC : HasEnoughKInjectives C) :
    (kInjectiveLocalizer C).IsLocalizedEquivalence := by
  sorry

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
variable [Abelian C₁] [Abelian C₂] [Abelian C₃]

/-- Restrict a bifunctor on complexes to K-injective complexes in both variables. -/
abbrev restrict₂KInjective (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) :
    KInjectiveComplex C₁ × KInjectiveComplex C₂ ⥤ Complex C₃ :=
  ((kInjectiveInclusion C₁).prod (kInjectiveInclusion C₂)) ⋙ Functor.uncurry.obj T

/-- The condition that a bifunctor sends quasi-isomorphisms between K-injective complexes in both
variables to quasi-isomorphisms after localization. -/
abbrev InvertsKInjectiveQuasiIso₂ (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) : Prop :=
  ((kInjectiveQuasiIso C₁).prod (kInjectiveQuasiIso C₂)).IsInvertedBy
    (restrict₂KInjective T ⋙ DerivedCategory.Q)

/-- The functor on the localized categories of K-injective complexes induced by a bifunctor. -/
noncomputable def localized₂ByKInjectives (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKInjectiveQuasiIso₂ T) :
    (kInjectiveQuasiIso C₁).Localization × (kInjectiveQuasiIso C₂).Localization ⥤
      DerivedCategory C₃ :=
  Localization.lift (restrict₂KInjective T ⋙ DerivedCategory.Q) hT
    ((kInjectiveQuasiIso C₁).Q.prod (kInjectiveQuasiIso C₂).Q)

/-- If K-injective complexes compute the derived category, their localized category is equivalent
to the usual derived category. -/
noncomputable def kInjectiveLocalizationEquivalence
    (C : Type u₁) [Category.{v₁} C] [Abelian C] (hC : HasEnoughKInjectives C) :
    (kInjectiveQuasiIso C).Localization ≌ DerivedCategory C := by
  letI : (kInjectiveLocalizer C).IsLocalizedEquivalence :=
    kInjectiveLocalizer_isLocalizedEquivalence_of_hasEnoughKInjectives C hC
  exact ((kInjectiveLocalizer C).localizedFunctor (kInjectiveQuasiIso C).Q
    DerivedCategory.Q).asEquivalence

/-- The two-variable right-derived functor computed by K-injective replacements. -/
noncomputable def rightDerived₂ByKInjectives (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKInjectiveQuasiIso₂ T)
    (hC₁ : HasEnoughKInjectives C₁) (hC₂ : HasEnoughKInjectives C₂) :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  ((kInjectiveLocalizationEquivalence C₁ hC₁).inverse.prod
      (kInjectiveLocalizationEquivalence C₂ hC₂).inverse) ⋙
    localized₂ByKInjectives T hT

/-- Curried form of `rightDerived₂ByKInjectives`. -/
noncomputable def rightDerived₂ByKInjectivesCurried
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKInjectiveQuasiIso₂ T)
    (hC₁ : HasEnoughKInjectives C₁) (hC₂ : HasEnoughKInjectives C₂) :
    DerivedCategory C₁ ⥤ DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  Functor.curry.obj (rightDerived₂ByKInjectives T hT hC₁ hC₂)

end KInjective

section KFlat

/-- A K-flat complex is a complex for which tensoring on either side preserves quasi-isomorphisms.
This definition is phrased relative to a monoidal structure on the category of cochain complexes. -/
class IsKFlat {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] (K : Complex C) : Prop where
  tensorLeft_quasiIso {X Y : Complex C} (f : X ⟶ Y) (hf : W C f) :
    W C ((tensorLeft K).map f)
  tensorRight_quasiIso {X Y : Complex C} (f : X ⟶ Y) (hf : W C f) :
    W C ((tensorRight K).map f)

/-- The object property of being K-flat. -/
abbrev kFlatComplexes (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] : ObjectProperty (Complex C) :=
  fun K => IsKFlat K

/-- The full subcategory of K-flat cochain complexes. -/
abbrev KFlatComplex (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] :=
  (kFlatComplexes C).FullSubcategory

/-- The inclusion of K-flat complexes. -/
abbrev kFlatInclusion (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] : KFlatComplex C ⥤ Complex C :=
  (kFlatComplexes C).ι

/-- Quasi-isomorphisms between K-flat complexes. -/
abbrev kFlatQuasiIso (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] : MorphismProperty (KFlatComplex C) :=
  (W C).inverseImage (kFlatInclusion C)

/-- The inclusion of K-flat complexes as a morphism of localizers. -/
def kFlatLocalizer (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] : LocalizerMorphism (kFlatQuasiIso C) (W C) where
  functor := kFlatInclusion C
  map _ _ _ hf := hf

/-- A K-flat resolution of a complex `K` is a quasi-isomorphism `F ⟶ K` from a K-flat complex. -/
def HasKFlatResolution {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] (K : Complex C) : Prop :=
  ∃ (F : Complex C), IsKFlat F ∧ ∃ q : F ⟶ K, W C q

/-- The concrete enough-K-flats hypothesis: every complex has a K-flat resolution. -/
abbrev HasEnoughKFlats (C : Type u₁) [Category.{v₁} C] [Abelian C]
    [MonoidalCategory (Complex C)] : Prop :=
  ∀ K : Complex C, HasKFlatResolution K

/-- If every K-projective complex is K-flat, then enough K-projective resolutions give enough
K-flat resolutions. -/
lemma hasEnoughKFlats_of_hasEnoughKProjectives
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory (Complex C)]
    (hC : HasEnoughKProjectives C)
    (hflat : ∀ K : Complex C, CochainComplex.IsKProjective K → IsKFlat K) :
    HasEnoughKFlats C := by
  intro K
  rcases hC K with ⟨P, hP, q, hq⟩
  exact ⟨P, hflat P hP, q, hq⟩

/-- Obligation: enough K-flat resolutions imply that K-flat complexes compute the derived category. -/
lemma kFlatLocalizer_isLocalizedEquivalence_of_hasEnoughKFlats
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory (Complex C)]
    (hC : HasEnoughKFlats C) :
    (kFlatLocalizer C).IsLocalizedEquivalence := by
  sorry

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
variable [Abelian C₁] [Abelian C₂] [Abelian C₃]
variable [MonoidalCategory (Complex C₁)] [MonoidalCategory (Complex C₂)]

/-- Restrict a bifunctor on complexes to K-flat complexes in both variables. -/
abbrev restrict₂KFlat (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) :
    KFlatComplex C₁ × KFlatComplex C₂ ⥤ Complex C₃ :=
  ((kFlatInclusion C₁).prod (kFlatInclusion C₂)) ⋙ Functor.uncurry.obj T

/-- The condition that a bifunctor sends quasi-isomorphisms between K-flat complexes in both
variables to quasi-isomorphisms after localization. -/
abbrev InvertsKFlatQuasiIso₂ (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) : Prop :=
  ((kFlatQuasiIso C₁).prod (kFlatQuasiIso C₂)).IsInvertedBy
    (restrict₂KFlat T ⋙ DerivedCategory.Q)

/-- The tensor product bifunctor sends quasi-isomorphisms between K-flat complexes in both
variables to quasi-isomorphisms. -/
lemma curriedTensor_invertsKFlatQuasiIso₂
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory (Complex C)] :
    InvertsKFlatQuasiIso₂ (C₁ := C) (C₂ := C) (C₃ := C) (curriedTensor (Complex C)) := by
  intro X Y f hf
  let f' := ((kFlatInclusion C).prod (kFlatInclusion C)).map f
  have hW : W C ((Functor.uncurry.obj (curriedTensor (Complex C))).map f') := by
    rw [Functor.uncurry_obj_map]
    dsimp [f'] at hf ⊢
    simp only [Functor.prod_map]
    haveI : IsKFlat X.2.1 := X.2.2
    haveI : IsKFlat Y.1.1 := Y.1.2
    let φ := ((curriedTensor (Complex C)).map ((kFlatInclusion C).map f.1)).app X.2.1
    let ψ := ((curriedTensor (Complex C)).obj Y.1.1).map ((kFlatInclusion C).map f.2)
    have h₁ : QuasiIso φ := by
      dsimp [φ]
      change W C (((curriedTensor (Complex C)).map ((kFlatInclusion C).map f.1)).app X.2.1)
      exact IsKFlat.tensorRight_quasiIso ((kFlatInclusion C).map f.1) hf.1
    have h₂ : QuasiIso ψ := by
      dsimp [ψ]
      change W C (((curriedTensor (Complex C)).obj Y.1.1).map ((kFlatInclusion C).map f.2))
      exact IsKFlat.tensorLeft_quasiIso ((kFlatInclusion C).map f.2) hf.2
    change QuasiIso (φ ≫ ψ)
    constructor
    intro i
    exact @quasiIsoAt_comp ℤ C _ _ (ComplexShape.up ℤ) _ _ _ φ ψ i _ _ _
      (h₁.quasiIsoAt i) (h₂.quasiIsoAt i)
  exact Localization.inverts DerivedCategory.Q (W C) _ hW

/-- The functor on the localized categories of K-flat complexes induced by a bifunctor. -/
noncomputable def localized₂ByKFlats (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKFlatQuasiIso₂ T) :
    (kFlatQuasiIso C₁).Localization × (kFlatQuasiIso C₂).Localization ⥤
      DerivedCategory C₃ :=
  Localization.lift (restrict₂KFlat T ⋙ DerivedCategory.Q) hT
    ((kFlatQuasiIso C₁).Q.prod (kFlatQuasiIso C₂).Q)

/-- If K-flat complexes compute the derived category, their localized category is equivalent to the
usual derived category. -/
noncomputable def kFlatLocalizationEquivalence
    (C : Type u₁) [Category.{v₁} C] [Abelian C] [MonoidalCategory (Complex C)]
    (hC : HasEnoughKFlats C) :
    (kFlatQuasiIso C).Localization ≌ DerivedCategory C := by
  letI : (kFlatLocalizer C).IsLocalizedEquivalence :=
    kFlatLocalizer_isLocalizedEquivalence_of_hasEnoughKFlats C hC
  exact ((kFlatLocalizer C).localizedFunctor (kFlatQuasiIso C).Q DerivedCategory.Q).asEquivalence

/-- The two-variable left-derived functor computed by K-flat replacements. -/
noncomputable def leftDerived₂ByKFlats (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKFlatQuasiIso₂ T)
    (hC₁ : HasEnoughKFlats C₁) (hC₂ : HasEnoughKFlats C₂) :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  ((kFlatLocalizationEquivalence C₁ hC₁).inverse.prod
      (kFlatLocalizationEquivalence C₂ hC₂).inverse) ⋙ localized₂ByKFlats T hT

/-- Curried form of `leftDerived₂ByKFlats`. -/
noncomputable def leftDerived₂ByKFlatsCurried
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsKFlatQuasiIso₂ T)
    (hC₁ : HasEnoughKFlats C₁) (hC₂ : HasEnoughKFlats C₂) :
    DerivedCategory C₁ ⥤ DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  Functor.curry.obj (leftDerived₂ByKFlats T hT hC₁ hC₂)

end KFlat

end TwoVariable
end DerivedCategory
end CategoryTheory
