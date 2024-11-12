/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import LeanCondensed.LightCondensed.SequentialLimit
/-!

# Project: AB axioms, light condensed abelian groups has countable AB4*, etc.

-/

open CategoryTheory Limits ShortComplex

universe v u w

namespace CategoryTheory.Limits

section

variable (I : Type*) [Category I]
variable (A : Type*) [Category A] [Abelian A]

-- I guess this API has been removed?
-- example (S : ShortComplex A) (h : S.Exact) : Exact S.f S.g := by
--   rwa [exact_iff_shortComplex_exact S]

example : I ⥤ ShortComplex A ≌ ShortComplex (I ⥤ A) :=
  (functorEquivalence I A).symm

lemma forall_exact_iff_functorEquivalence_exact (F : I ⥤ ShortComplex A) : (∀ i, (F.obj i).Exact) ↔
    ((functorEquivalence I A).inverse.obj F).Exact := by
  sorry

class HasExactLimitsOfShape : Prop where
  hasLimitsOfShape : HasLimitsOfShape I A := by infer_instance
  exact_limit (F : I ⥤ ShortComplex A) : (∀ i, (F.obj i).ShortExact) → (limit F).ShortExact

attribute [instance] HasExactLimitsOfShape.hasLimitsOfShape

instance [HasLimitsOfShape I A] [PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)] :
    HasExactLimitsOfShape I A where
  exact_limit := sorry

instance [HasExactLimitsOfShape I A] : PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A) := sorry

lemma hasExactLimitsOfShape_iff_lim_rightExact [HasLimitsOfShape I A] :
    HasExactLimitsOfShape I A ↔ Nonempty (PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)) :=
  ⟨fun _ ↦ ⟨inferInstance⟩, fun ⟨_⟩ ↦ inferInstance⟩

lemma hasExactLimitsOfShape_iff_limitCone_shortExact [HasLimitsOfShape I A] :
    HasExactLimitsOfShape I A ↔
      ∀ (F : I ⥤ ShortComplex A), ((∀ i, (F.obj i).ShortExact) → (limitCone F).pt.ShortExact) := by
  constructor
  · exact fun ⟨_, h₁⟩ F h₂ ↦ shortExact_of_iso
      ((limit.isLimit F).conePointUniqueUpToIso (isLimitLimitCone F)) ((h₁ F) h₂)
  · exact fun h ↦ ⟨inferInstance, fun F hh ↦ shortExact_of_iso
      ((isLimitLimitCone F).conePointUniqueUpToIso (limit.isLimit F)) (h F hh)⟩

class HasExactColimitsOfShape : Prop where
  hasColimitsOfShape : HasColimitsOfShape I A := by infer_instance
  exact_colimit (F : I ⥤ ShortComplex A) : ((∀ i, (F.obj i).ShortExact) → (colimit F).ShortExact)

attribute [instance] HasExactColimitsOfShape.hasColimitsOfShape

instance [HasColimitsOfShape I A] [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)] :
    HasExactColimitsOfShape I A where
  exact_colimit := sorry

instance [HasExactColimitsOfShape I A] : PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A) := sorry

lemma hasExactColimitsOfShape_iff_colim_leftExact [HasLimitsOfShape I A] :
    HasExactLimitsOfShape I A ↔ Nonempty (PreservesFiniteColimits (lim : (I ⥤ A) ⥤ A)) :=
  ⟨fun _ ↦ ⟨inferInstance⟩, fun ⟨_⟩ ↦ inferInstance⟩

lemma hasExactColimitsOfShape_iff_colimitCocone_shortExact [HasColimitsOfShape I A] :
    HasExactColimitsOfShape I A ↔ ∀ (F : I ⥤ ShortComplex A),
      ((∀ i, (F.obj i).ShortExact) → (colimitCocone F).pt.ShortExact) := by
  constructor
  · exact fun ⟨_, h₁⟩ F h₂ ↦ shortExact_of_iso
      ((colimit.isColimit F).coconePointUniqueUpToIso (isColimitColimitCocone F)) ((h₁ F) h₂)
  · exact fun h ↦ ⟨inferInstance, fun F hh ↦ shortExact_of_iso
      ((isColimitColimitCocone F).coconePointUniqueUpToIso (colimit.isColimit F)) (h F hh)⟩

end

section

variable (A : Type u) [Category.{v} A] [Abelian A]

abbrev AB4 : Prop := ∀ (I : Type w), HasExactColimitsOfShape (Discrete I) A

abbrev AB4star : Prop := ∀ (I : Type w), HasExactLimitsOfShape (Discrete I) A

abbrev countableAB4star : Prop := ∀ (I : Type) [Countable I], HasExactLimitsOfShape (Discrete I) A

abbrev sequentialAB4star : Prop := HasExactLimitsOfShape ℕᵒᵖ A

lemma countableAB4star_of_sequentialAB4star [sequentialAB4star A] : countableAB4star A := sorry

abbrev AB5 : Prop := ∀ (I : Type v) [SmallCategory I] [IsFiltered I], HasExactColimitsOfShape I A

end

section

variable (A : Type*) [Category A] [Abelian A]
variable (I : Type*) [Category I]

lemma mono_of_mono [HasLimitsOfShape I A] (F : I ⥤ ShortComplex A) (h : ∀ i, Mono (F.obj i).f) :
    Mono (ShortComplex.limitCone F).pt.f := by
  simp only [ShortComplex.limitCone, Functor.const_obj_obj]
  have : Mono (whiskerLeft F ShortComplex.π₁Toπ₂) := by
    apply (config := {allowSynthFailures := true}) NatTrans.mono_of_mono_app
    exact h
  infer_instance

lemma left_exact_of_left_exact [HasLimitsOfShape I A] (F : I ⥤ ShortComplex A)
    (h : ∀ i, Mono (F.obj i).f ∧ (F.obj i).Exact) :
    Mono (ShortComplex.limitCone F).pt.f ∧ (ShortComplex.limitCone F).pt.Exact := by
  sorry

lemma right_exact_of_right_exact [HasColimitsOfShape I A] (F : I ⥤ ShortComplex A)
    (h : ∀ i, Epi (F.obj i).g ∧ (F.obj i).Exact) :
    Epi (ShortComplex.colimitCocone F).pt.g ∧ (ShortComplex.colimitCocone F).pt.Exact := by
  sorry

lemma epi_of_epi [HasColimitsOfShape I A] (F : I ⥤ ShortComplex A) (h : ∀ i, Epi (F.obj i).g) :
    Epi (ShortComplex.colimitCocone F).pt.g := by
  simp only [ShortComplex.colimitCocone, Functor.const_obj_obj]
  have : Epi (whiskerLeft F ShortComplex.π₂Toπ₃) := by
    apply (config := {allowSynthFailures := true}) NatTrans.epi_of_epi_app
    exact h
  infer_instance

lemma abStar_iff_preserves_epi'' [HasLimitsOfShape I A] :
    (∀ (F G : I ⥤ A) (α : F ⟶ G), (∀ i, Epi (α.app i)) → Epi (limMap α)) ↔
    HasExactLimitsOfShape I A := by
  sorry

lemma abStar_iff_preserves_epi [HasLimitsOfShape I A] :
    ((∀ (F : I ⥤ ShortComplex A),
      (∀ i, (F.obj i).ShortExact) → Epi (ShortComplex.limitCone F).pt.g)) ↔
    HasExactLimitsOfShape I A := by
  rw [hasExactLimitsOfShape_iff_limitCone_shortExact]
  constructor
  · intro h F hh
    have := ShortExact.mk' (S := (limitCone F).pt)
    rw [← and_imp] at this
    apply this
    · rw [and_comm]
      apply left_exact_of_left_exact
      exact fun i ↦ ⟨(hh i).mono_f, (hh i).1⟩
    · exact h _ hh
  · exact fun h F hh ↦ (h F hh).epi_g

lemma ab_iff_preserves_mono [HasColimitsOfShape I A] :
    ((∀ (F : I ⥤ ShortComplex A),
    (∀ i, (F.obj i).ShortExact) → Mono (ShortComplex.colimitCocone F).pt.f)) ↔
      HasExactColimitsOfShape I A := by
  rw [hasExactColimitsOfShape_iff_colimitCocone_shortExact]
  constructor
  · intro h F hh
    have := ShortExact.mk' (S := (colimitCocone F).pt)
    rw [Imp.swap (a := Mono (colimitCocone F).pt.f), ← and_imp] at this
    apply this
    · rw [and_comm]
      apply right_exact_of_right_exact
      exact fun i ↦ ⟨(hh i).epi_g, (hh i).1⟩
    · exact h _ hh
  · exact fun h F hh ↦ (h F hh).mono_f

lemma finite_abStar (I : Type) [Finite I] : HasExactLimitsOfShape (Discrete I) A := by sorry

lemma finite_ab (I : Type) [Finite I] : HasExactColimitsOfShape (Discrete I) A := sorry

lemma sequentialAB4star_of_epi_limit_of_epi
  (h : ∀ (F : ℕᵒᵖ ⥤ A) (c : Cone F) (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)), Epi (c.π.app ⟨0⟩)) :
    sequentialAB4star A := sorry

end

end CategoryTheory.Limits

namespace LightCondensed

variable (R : Type u) [Ring R]

instance : sequentialAB4star (LightCondMod.{u} R) := by
  apply sequentialAB4star_of_epi_limit_of_epi
  intro _ _ hc hF
  exact LightCondMod.epi_π_app_zero_of_epi _ hc hF

-- the goal:
instance : countableAB4star (LightCondMod.{u} R) := countableAB4star_of_sequentialAB4star _

end LightCondensed
