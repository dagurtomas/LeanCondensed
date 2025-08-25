/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Mathlib.CategoryTheory.Sites.Monoidal
import LeanCondensed.Projects.MonoidalLinear
import LeanCondensed.Projects.SheafMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.Condensed.CartesianClosed
import Mathlib.Condensed.Module

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory
  Functor

namespace Condensed

variable (R : Type (u + 1)) [CommRing R]

attribute [local instance] monoidalCategory in
instance : MonoidalCategory (CondensedMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Sheaf _ _))

instance : MonoidalCategory (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u+1} R)) :=
  inferInstanceAs (MonoidalCategory (CondensedMod.{u} R))

attribute [local instance] monoidalCategory symmetricCategory in
instance : SymmetricCategory (CondensedMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Sheaf _ _))

attribute [local instance] monoidalCategory in
def monoidalClosedSheaves : MonoidalClosed
    (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

attribute [local instance] monoidalCategory monoidalClosedSheaves in
instance : MonoidalClosed (CondensedMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Sheaf _ _))

instance : (free R).Monoidal :=
  inferInstanceAs (Sheaf.composeAndSheafify _ (ModuleCat.free R)).Monoidal

attribute [local instance] monoidalCategory CategoryTheory.Sheaf.monoidalPreadditive in
instance : MonoidalPreadditive (CondensedMod.{u} R) :=
  inferInstanceAs (MonoidalPreadditive (Sheaf _ _))

end Condensed
