/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Module
import LeanCondensed.Epi.LightCondensed
import LeanCondensed.LightProfinite.SequentialLimit
import LeanCondensed.Misc.NatFunctor
/-!

# Limits of epimorphisms in `LightCondMod R`

This file proves that a sequential limit of epimorhpisms is epimorphic in `LightCondMod R`
In other words, given epis
`⋯ ⟶ Sₙ₊₁ ⟶ Sₙ ⟶ ⋯ ⟶ S₀`,
the projection map `lim Sₙ ⟶ S₀` is surjective.
-/

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightCondensed

private noncomputable def preimage (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) :
    (n : ℕ) → ((T : LightProfinite) × (F.obj ⟨n⟩).val.obj ⟨T⟩)
  | 0 => ⟨S, g⟩
  | (n+1) =>
    have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
      (preimage R c hF S g n).1 (preimage R c hF S g n).2
    ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimage_transitionMap
  (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) :
    (n : ℕ) → ((preimage R c hF S g (n+1)).1 ⟶ (preimage R c hF S g n).1) := sorry

private noncomputable def preimage_diagram
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) : ℕᵒᵖ ⥤ LightProfinite :=
  Nat.functor_mk (fun n ↦ (preimage R c hF S g n).1) fun n ↦ preimage_transitionMap R c hF S g n

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

lemma epi_limit_of_epi : Epi (c.π.app ⟨0⟩) := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro S g
  refine ⟨limit (preimage_diagram R c hF S g), limit.π (preimage_diagram R c hF S g) ⟨0⟩,
    LightProfinite.limit_of_surjections_surjective (limit.isLimit _) ?_, ?_⟩
  · sorry
  · sorry
    -- we need to regard the `S` valued points of a light condensed module `A` as maps
    -- `S ⟶ (forget R).obj A` Then we can use `hc.lift (lightProfiniteToCondensed.mapCone _)` 
