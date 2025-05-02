/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Sites.Monoidal
import LeanCondensed.Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-!
# Monoidal category structure on categories of sheaves

If `A` is a closed braided category with suitable limits,
and `J` is a Grothendieck topology with `HasWeakSheafify J A`,
then `Sheaf J A` can be equipped with a monoidal category
structure. This is not made an instance as in some cases
it may conflict with monoidal structure deduced from
chosen finite products.

## TODO

* show that the monoidal category structure on sheaves is closed,
and that the internal hom can be defined in such a way that the
underlying presheaf is the internal hom in the category of presheaves.
Note that a `MonoidalClosed` instance on sheaves can already be obtained
abstractly using the material in `CategoryTheory.Monoidal.Braided.Reflection`.

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {A : Type u} [Category.{v} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Sheaf

variable (J A)

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
braided when `A` is braided. -/
noncomputable def braidedCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [BraidedCategory A] :
    letI := monoidalCategory J A
    BraidedCategory (Sheaf J A) :=
  inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
symmetric when `A` is symmetric. -/
noncomputable def symmetricCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [SymmetricCategory A] :
    letI := monoidalCategory J A
    SymmetricCategory (Sheaf J A) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [BraidedCategory A] :
    letI := monoidalCategory J A
    letI := braidedCategory J A
    (presheafToSheaf J A).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Braided

end Sheaf

end CategoryTheory
