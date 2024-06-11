/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# The light profinite set classifying convergent sequences

This files defines the light profinite set `ℕ∪{∞}`, defined as the one point compactification of
`ℕ`.
-/

open CategoryTheory TopologicalSpace OnePoint

namespace OnePoint

open Filter Topology Set

protected lemma «forall» {X : Type*} {p : OnePoint X → Prop} :
    (∀ (x : OnePoint X), p x) ↔ p ∞ ∧ ∀ (x : X), p (some x) :=
  Option.forall

lemma continuous_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : OnePoint X → Y) : Continuous f ↔
    Tendsto (fun x : X ↦ f x) (coclosedCompact X) (𝓝 (f ∞)) ∧ Continuous (fun x : X ↦ f x) := by
  simp_rw [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty']
  rfl

lemma continuous_iff_of_discrete {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology X] (f : OnePoint X → Y) :
    Continuous f ↔ Tendsto (fun x : X ↦ f x) cofinite (𝓝 (f ∞)) := by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

lemma continuous_iff_of_nat {Y : Type*} [TopologicalSpace Y] (f : OnePoint ℕ → Y) :
    Continuous f ↔ Tendsto (fun x : ℕ ↦ f x) atTop (𝓝 (f ∞)) := by
  rw [continuous_iff_of_discrete, Nat.cofinite_eq_atTop]

instance (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallySeparatedSpace (OnePoint X) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | none =>
      refine ⟨{y}ᶜ, {y}, isOpen_compl_singleton, ?_, hxy, rfl, (compl_union_self _).symm.subset,
        disjoint_compl_left⟩
      rw [OnePoint.isOpen_iff_of_not_mem]
      exacts [isOpen_discrete _, hxy]
    | some val =>
      refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, rfl, hxy.symm, by simp,
        disjoint_compl_right⟩
      rw [OnePoint.isOpen_iff_of_not_mem]
      exacts [isOpen_discrete _, (Option.some_ne_none val).symm]

instance (X : Type*) [TopologicalSpace X] [c : CompactSpace X] [MetrizableSpace X] :
    SecondCountableTopology X := by
  obtain ⟨_, h⟩ := MetrizableSpace.exists_metric (X := X)
  rw [← h] at c ⊢
  infer_instance

end OnePoint

namespace LightProfinite

/-- The continuous map from `ℕ∪{∞}` to `ℝ` sending `n` to `1/(n+1)` and `∞` to `0`. -/
noncomputable def natUnionInftyEmbedding : C(OnePoint ℕ, ℝ) where
  toFun
    | ∞ => 0
    | OnePoint.some n => 1 / (n+1 : ℝ)
  continuous_toFun := OnePoint.continuous_iff_of_nat _ |>.mpr
    tendsto_one_div_add_atTop_nhds_zero_nat

/--
The continuous map from `ℕ∪{∞}` to `ℝ` sending `n` to `1/(n+1)` and `∞` to `0` is a closed
embedding.
-/
lemma closedEmbedding_natUnionInftyEmbedding : ClosedEmbedding natUnionInftyEmbedding := by
  refine closedEmbedding_of_continuous_injective_closed
    natUnionInftyEmbedding.continuous ?_ ?_
  · rintro (_|n) (_|m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      rw [← Nat.cast_one, ← Nat.cast_add, eq_comm, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · exact fun _ hC => (hC.isCompact.image natUnionInftyEmbedding.continuous).isClosed

instance : MetrizableSpace (OnePoint ℕ) := closedEmbedding_natUnionInftyEmbedding.metrizableSpace

/-- The one point compactification of the natural numbers as a light profinite set. -/
abbrev NatUnionInfty : LightProfinite := of (OnePoint ℕ)

@[inherit_doc]
scoped notation "ℕ∪{∞}" => NatUnionInfty

instance : Coe ℕ ℕ∪{∞} := optionCoe

open Filter Topology

lemma continuous_iff_convergent {Y : Type*} [TopologicalSpace Y] (f : ℕ∪{∞} → Y) :
    Continuous f ↔ Tendsto (fun x : ℕ ↦ f x) atTop (𝓝 (f ∞)) :=
  continuous_iff_of_nat f

end LightProfinite
