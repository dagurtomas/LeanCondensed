/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Two-variable derived functors from adapted replacements

This file is a general scaffold for constructing derived bifunctors. The input is a bifunctor on
cochain complexes

```
T : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex C₃ ℤ
```

together with two object properties `P₁`, `P₂` of complexes, thought of as the adapted objects
(K-projective, K-injective, K-flat, ...). If `T`, restricted to `P₁ × P₂`, sends pairs of adapted
quasi-isomorphisms to quasi-isomorphisms, and if the inclusions of adapted objects induce
equivalences after localizing at quasi-isomorphisms, then `derived₂` produces a functor

```
DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃.
```

The point of the setup is that the hard category-specific input is isolated into typeclass
assumptions about the chosen adapted properties. For example, in a category with enough
K-projective replacements one should use `kProjective`; for right-derived constructions one should
use `kInjective`; and a future/available K-flat API can be plugged in as another
`AdaptedProperty`.
-/

noncomputable section

open CategoryTheory Limits
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

/-- An adapted class of complexes used to compute derived functors. -/
abbrev AdaptedProperty (C : Type u₁) [Category.{v₁} C] [Abelian C] :=
  ObjectProperty (Complex C)

/-- The quasi-isomorphisms in the full subcategory of adapted complexes. -/
abbrev adaptedQuasiIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (P : AdaptedProperty C) : MorphismProperty P.FullSubcategory :=
  (W C).inverseImage P.ι

/-- The inclusion of adapted complexes as a morphism of localizers. -/
def adaptedLocalizer {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (P : AdaptedProperty C) : LocalizerMorphism (adaptedQuasiIso P) (W C) where
  functor := P.ι
  map _ _ _ hf := hf

/-- `P` has enough left adapted resolutions, in the sense of localization derivability structures. -/
abbrev IsLeftAdapted {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (P : AdaptedProperty C) : Prop :=
  (adaptedLocalizer P).IsLeftDerivabilityStructure

/-- `P` has enough right adapted resolutions, in the sense of localization derivability structures. -/
abbrev IsRightAdapted {C : Type u₁} [Category.{v₁} C] [Abelian C]
    (P : AdaptedProperty C) : Prop :=
  (adaptedLocalizer P).IsRightDerivabilityStructure

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
variable [Abelian C₁] [Abelian C₂] [Abelian C₃]

/-- Restrict a bifunctor on complexes to adapted complexes in both variables. -/
abbrev restrict₂ (P₁ : AdaptedProperty C₁) (P₂ : AdaptedProperty C₂)
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) :
    P₁.FullSubcategory × P₂.FullSubcategory ⥤ Complex C₃ :=
  (P₁.ι.prod P₂.ι) ⋙ Functor.uncurry.obj T

/-- The condition that `T`, on adapted objects, sends adapted quasi-isomorphisms in both variables
to quasi-isomorphisms after passing to `DerivedCategory C₃`. -/
abbrev InvertsAdaptedQuasiIso₂ (P₁ : AdaptedProperty C₁) (P₂ : AdaptedProperty C₂)
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃) : Prop :=
  ((adaptedQuasiIso P₁).prod (adaptedQuasiIso P₂)).IsInvertedBy
    (restrict₂ P₁ P₂ T ⋙ DerivedCategory.Q)

/-- The functor on the localized categories of adapted complexes induced by `T`. -/
noncomputable def adaptedDerived₂ (P₁ : AdaptedProperty C₁) (P₂ : AdaptedProperty C₂)
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsAdaptedQuasiIso₂ P₁ P₂ T) :
    (adaptedQuasiIso P₁).Localization × (adaptedQuasiIso P₂).Localization ⥤ DerivedCategory C₃ :=
  Localization.lift (restrict₂ P₁ P₂ T ⋙ DerivedCategory.Q) hT
    ((adaptedQuasiIso P₁).Q.prod (adaptedQuasiIso P₂).Q)

/-- If adapted complexes compute the derived category, their localized category is equivalent to the
usual derived category. -/
noncomputable def adaptedLocalizationEquivalence (P : AdaptedProperty C₁)
    [(adaptedLocalizer P).IsLocalizedEquivalence] :
    (adaptedQuasiIso P).Localization ≌ DerivedCategory C₁ :=
  ((adaptedLocalizer P).localizedFunctor (adaptedQuasiIso P).Q DerivedCategory.Q).asEquivalence

/-- The two-variable derived functor computed by adapted replacements in both variables. -/
noncomputable def derived₂ (P₁ : AdaptedProperty C₁) (P₂ : AdaptedProperty C₂)
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsAdaptedQuasiIso₂ P₁ P₂ T)
    [(adaptedLocalizer P₁).IsLocalizedEquivalence]
    [(adaptedLocalizer P₂).IsLocalizedEquivalence] :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  ((adaptedLocalizationEquivalence P₁).inverse.prod
      (adaptedLocalizationEquivalence P₂).inverse) ⋙ adaptedDerived₂ P₁ P₂ T hT

/-- Curried form of `derived₂`, convenient for monoidal closed applications. -/
noncomputable def derived₂Curried (P₁ : AdaptedProperty C₁) (P₂ : AdaptedProperty C₂)
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsAdaptedQuasiIso₂ P₁ P₂ T)
    [(adaptedLocalizer P₁).IsLocalizedEquivalence]
    [(adaptedLocalizer P₂).IsLocalizedEquivalence] :
    DerivedCategory C₁ ⥤ DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  Functor.curry.obj (derived₂ P₁ P₂ T hT)

/-- The adapted property of K-projective complexes. -/
abbrev kProjective (C : Type u₁) [Category.{v₁} C] [Abelian C] : AdaptedProperty C :=
  fun K => CochainComplex.IsKProjective K

/-- The adapted property of K-injective complexes. -/
abbrev kInjective (C : Type u₁) [Category.{v₁} C] [Abelian C] : AdaptedProperty C :=
  fun K => CochainComplex.IsKInjective K

/-- Left-derived bifunctor computed using K-projective replacements in both variables, assuming the
ambient categories have enough such replacements and `T` respects quasi-isomorphisms between them. -/
noncomputable abbrev leftDerived₂ByKProjectives
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsAdaptedQuasiIso₂ (kProjective C₁) (kProjective C₂) T)
    [(adaptedLocalizer (kProjective C₁)).IsLocalizedEquivalence]
    [(adaptedLocalizer (kProjective C₂)).IsLocalizedEquivalence] :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  derived₂ (kProjective C₁) (kProjective C₂) T hT

/-- Right-derived bifunctor computed using K-injective replacements in both variables, assuming the
ambient categories have enough such replacements and `T` respects quasi-isomorphisms between them. -/
noncomputable abbrev rightDerived₂ByKInjectives
    (T : Complex C₁ ⥤ Complex C₂ ⥤ Complex C₃)
    (hT : InvertsAdaptedQuasiIso₂ (kInjective C₁) (kInjective C₂) T)
    [(adaptedLocalizer (kInjective C₁)).IsLocalizedEquivalence]
    [(adaptedLocalizer (kInjective C₂)).IsLocalizedEquivalence] :
    DerivedCategory C₁ × DerivedCategory C₂ ⥤ DerivedCategory C₃ :=
  derived₂ (kInjective C₁) (kInjective C₂) T hT

end TwoVariable
end DerivedCategory
end CategoryTheory
