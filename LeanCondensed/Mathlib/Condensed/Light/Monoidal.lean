/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.Condensed.Discrete.Module
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
public import Mathlib.Condensed.Light.Monoidal
public import Mathlib.Condensed.Light.Small
public import LeanCondensed.Projects.MonoidalLinear

@[expose] public section

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

variable (R : Type u) [CommRing R]

instance : MonoidalPreadditive (LightCondMod.{u} R) :=
  CategoryTheory.Sheaf.monoidalPreadditive _ _

end LightCondensed
