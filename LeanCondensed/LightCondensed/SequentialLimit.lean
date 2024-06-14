/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Module
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

variable (R : Type*) [Ring R]

variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

lemma epi_limit_of_epi : Epi (c.π.app ⟨0⟩) := sorry
