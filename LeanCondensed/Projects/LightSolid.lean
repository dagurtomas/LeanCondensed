/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.InternallyProjective
/-!

# Project: light solid abelian groups

* Define the condensed abelian group / module called `P`. This is `ℤ[ℕ∪{∞}]/(∞)`, the light
  condensed abelian group "classifying null sequences".

* Define `shift : P ⟶ P`.

* Define the property of a light condensed abelian group `A` of being solid as the fact that the
  natural map of internal homs from `P` to `A` induced by `1 - shift` is an iso.

-/
