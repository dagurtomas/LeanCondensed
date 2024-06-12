/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

instance : R.IsLeftKanExtension adj.unit where
  nonempty_isUniversal := sorry

instance : L.IsRightKanExtension adj.counit := sorry
