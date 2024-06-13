/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Condensed.Light.Module
/-!

# Project: AB axioms, light condensed abelian groups has countable AB4*, etc.


-/

open CategoryTheory Limits ShortComplex

universe v u w

namespace CategoryTheory.Limits

section

variable (I : Type*) [Category I]
variable (A : Type*) [Category A] [Abelian A]
-- In the application, `A` is abelian, but `HasZeroMorphisms A` is the minimal condition
-- to state the AB axioms.

example (S : ShortComplex A) (h : S.Exact) : Exact S.f S.g := by
  rwa [exact_iff_shortComplex_exact S]

example : I ⥤ ShortComplex A ≌ ShortComplex (I ⥤ A) :=
  (functorEquivalence I A).symm

lemma forall_exact_iff_functorEquivalence_exact (F : I ⥤ ShortComplex A) : (∀ i, (F.obj i).Exact) ↔
    ((functorEquivalence I A).inverse.obj F).Exact := by
  sorry

class HasExactLimitsOfShape : Prop where
  hasLimitsOfShape : HasLimitsOfShape I A := by infer_instance
  exact_limit : ∀ (F : I ⥤ ShortComplex A), ∀ i, (F.obj i).ShortExact → (limit F).ShortExact

attribute [instance] HasExactLimitsOfShape.hasLimitsOfShape

instance [HasLimitsOfShape I A] [PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)] :
    HasExactLimitsOfShape I A where
  exact_limit := sorry

instance [HasExactLimitsOfShape I A] : PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A) := sorry

lemma hasExactLimitsOfShape_iff_lim_rightExact [HasLimitsOfShape I A] :
    HasExactLimitsOfShape I A ↔ Nonempty (PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)) :=
  ⟨fun _ ↦ ⟨inferInstance⟩, fun ⟨_⟩ ↦ inferInstance⟩

class HasExactColimitsOfShape : Prop where
  hasColimitsOfShape : HasColimitsOfShape I A := by infer_instance
  exact_colimit : ∀ (F : I ⥤ ShortComplex A), ∀ i, (F.obj i).ShortExact → (colimit F).ShortExact

attribute [instance] HasExactColimitsOfShape.hasColimitsOfShape

instance [HasColimitsOfShape I A] [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)] :
    HasExactColimitsOfShape I A where
  exact_colimit := sorry

instance [HasExactColimitsOfShape I A] : PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A) := sorry

lemma hasExactColimitsOfShape_iff_colim_leftExact [HasLimitsOfShape I A] :
    HasExactLimitsOfShape I A ↔ Nonempty (PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)) :=
  ⟨fun _ ↦ ⟨inferInstance⟩, fun ⟨_⟩ ↦ inferInstance⟩

end

section

variable (A : Type u) [Category.{v} A] [Abelian A]

abbrev AB4 : Prop := ∀ (I : Type w), HasExactColimitsOfShape (Discrete I) A

abbrev AB4star : Prop := ∀ (I : Type w), HasExactLimitsOfShape (Discrete I) A

abbrev countableAB4star : Prop := ∀ (I : Type) [Countable I], HasExactLimitsOfShape (Discrete I) A

abbrev AB5 : Prop := ∀ (I : Type v) [SmallCategory I] [IsFiltered I], HasExactColimitsOfShape I A

end

section

variable (A : Type*) [Category A] [Abelian A]
variable (I : Type*) [Category I] (F : I ⥤ ShortComplex A)

lemma mono_of_mono [HasLimitsOfShape I A] (h : ∀ i, Mono (F.obj i).f) :
    Mono (ShortComplex.limitCone F).pt.f := by
  simp only [ShortComplex.limitCone, Functor.const_obj_obj]
  have : Mono (whiskerLeft F ShortComplex.π₁Toπ₂) := by
    apply (config := {allowSynthFailures := true}) NatTrans.mono_of_mono_app
    exact h
  infer_instance

lemma left_exact_of_left_exact [HasLimitsOfShape I A]
    (h : ∀ i, Mono (F.obj i).f ∧ (F.obj i).Exact) :
    Mono (ShortComplex.limitCone F).pt.f ∧ (ShortComplex.limitCone F).pt.Exact := by
  sorry

lemma epi_of_epi [HasColimitsOfShape I A] (h : ∀ i, Epi (F.obj i).g) :
    Epi (ShortComplex.colimitCocone F).pt.g := by
  simp only [ShortComplex.colimitCocone, Functor.const_obj_obj]
  have : Epi (whiskerLeft F ShortComplex.π₂Toπ₃) := by
    apply (config := {allowSynthFailures := true}) NatTrans.epi_of_epi_app
    exact h
  infer_instance

-- Stating and proving the converse of this lemma should be easy
lemma abStar_of_preserves_epi [HasLimitsOfShape I A] (h : (∀ i, Epi (F.obj i).g) →
  Epi (ShortComplex.limitCone F).pt.g) : HasExactLimitsOfShape I A := sorry

-- Stating and proving the converse of this lemma should be easy
lemma ab_of_preserves_mono [HasColimitsOfShape I A] (h : (∀ i, Mono (F.obj i).f) →
  Epi (ShortComplex.colimitCocone F).pt.f) : HasExactColimitsOfShape I A := sorry

lemma finite_abStar (I : Type) [Finite I] : HasExactLimitsOfShape (Discrete I) A := sorry

lemma finite_ab (I : Type) [Finite I] : HasExactColimitsOfShape (Discrete I) A := sorry

end

end CategoryTheory.Limits

namespace LightCondensed

variable (R : Type u) [Ring R]

-- the goal (maybe we need some conditions on `R`):
instance : countableAB4star (LightCondMod.{u} R) := sorry

end LightCondensed
