/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.Monoidal
import Mathlib.Condensed.Light.Small
import LeanCondensed.Projects.MonoidalLinear

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : MonoidalPreadditive (LightCondMod.{u} R) :=
  CategoryTheory.Sheaf.monoidalPreadditive _ _

end LightCondensed
