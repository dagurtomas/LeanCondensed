/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Projects.DerivedSolid
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Derived solidification of free CW complexes

This file records the target comparison theorem: for a CW complex `X`, the homology of the derived
solidification of the free light condensed abelian group on `X` is integral singular homology.

The derived category is cohomologically indexed, so the `n`th singular homology group appears in
degree `-(n : ℤ)`.
-/

noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace LightCondensed
namespace Solid

/-- The free light condensed abelian group on a topological space. -/
noncomputable abbrev freeLightCondAbOfTop (X : TopCat) : LightCondAb :=
  (LightCondensed.free ℤ).obj X.toLightCondSet

/-- The derived solidification of the free light condensed abelian group on a topological space. -/
noncomputable abbrev derivedSolidificationOfTop (X : TopCat) : DSolid :=
  derivedSolidification.obj
    ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeLightCondAbOfTop X))

/-- Integral singular homology of a topological space, viewed as a discrete light condensed
abelian group. -/
noncomputable abbrev singularHomologyLightCondAb (X : TopCat) (n : ℕ) : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj X)

/-- For a CW complex `X`, the homology of the derived solidification of the free light condensed
abelian group on `X` is integral singular homology.  Since `DSolid` is cohomologically indexed, the
`n`th singular homology group occurs in degree `-n`. -/
noncomputable def derivedSolidification_free_CW_homologyIso
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    isSolid.ι.obj
      ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
        (derivedSolidificationOfTop X)) ≅
      singularHomologyLightCondAb X n := by
  sorry

/-- The theorem form of `derivedSolidification_free_CW_homologyIso`: the derived solidification of
the free light condensed abelian group on a CW complex computes integral singular homology. -/
theorem derivedSolidification_free_CW_homology
    (X : TopCat) [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Nonempty
      (isSolid.ι.obj
        ((DerivedCategory.homologyFunctor Solid (-(n : ℤ))).obj
          (derivedSolidificationOfTop X)) ≅
        singularHomologyLightCondAb X n) :=
  ⟨derivedSolidification_free_CW_homologyIso X n⟩

end Solid
end LightCondensed
