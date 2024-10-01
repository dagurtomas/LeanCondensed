/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Closed.Monoidal
/-!

# Project: prove that `ℤ[ℕ∪{∞}]` is internally projective in light condensed abelian groups

-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Limits

section InternallyProjective

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

class InternallyProjective (P : C) : Prop where
  preserves_epi : (ihom P).PreservesEpimorphisms

end InternallyProjective
