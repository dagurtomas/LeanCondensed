import Mathlib.Condensed.TopComparison

universe u

open CategoryTheory

namespace Condensed.LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHaus` given by locally constant maps.
-/
@[simps]
def functorToPresheaves : Type* ⥤ (CompHaus.{u}ᵒᵖ ⥤ Type _) where
  obj X := {
    obj := fun ⟨S⟩ ↦ LocallyConstant S X
    map := fun f g ↦ g.comap f.unop }
  map f := { app := fun S t ↦ t.map f }

/--
Locally constant maps are the same as continuous maps when the target is equipped with the discrete
topology
-/
@[simps]
def locallyConstantIsoContinuousMap (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := fun f ↦ (f : C(Y, X))
    inv := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

/-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
noncomputable def functorToPresheavesIsoTopCatToCondensed (X : Type (u+1)) :
    functorToPresheaves.obj X ≅ (topCatToCondensed.obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

/-- `Condensed.LocallyConstant.functorToPresheaves` lands in condensed sets. -/
@[simps]
def functor : Type (u+1) ⥤ CondensedSet.{u} where
  obj X := {
    val := functorToPresheaves.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIsoTopCatToCondensed X)]
      exact (topCatToCondensed.obj _).cond
  }
  map f := ⟨functorToPresheaves.map f⟩

/--
`Condensed.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToCondensed` to discrete topological spaces.
-/
noncomputable def functorIsoTopCatToCondensed : functor ≅ TopCat.discrete ⋙ topCatToCondensed := by
  refine NatIso.ofComponents (fun X ↦ (sheafToPresheaf _ _).preimageIso
    (functorToPresheavesIsoTopCatToCondensed X)) sorry
