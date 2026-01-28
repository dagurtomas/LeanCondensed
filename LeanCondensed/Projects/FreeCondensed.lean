import Mathlib

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits

attribute [local instance] Types.instConcreteCategory Types.instFunLike

namespace LightProfinite

namespace FreeImage

def set (Si : FintypeCat.{0}) (c : ℤ) : Set (Si →₀ ℤ) :=
  {a | ∑ i ∈ a.support, |a i| ≤ c }

instance (Si : FintypeCat.{0}) (c : ℤ) : Fintype (set Si c) :=
  sorry

def component (Si : FintypeCat.{0}) (c : ℤ) : LightProfinite :=
  FintypeCat.toLightProfinite.obj (FintypeCat.of (set Si c))

def functor (c : ℤ) : FintypeCat ⥤ LightProfinite where
  obj Si := component Si c
  map := sorry
  map_id := sorry
  map_comp := sorry

def profiniteComponent (S : LightProfinite.{0}) (c : ℤ) : LightProfinite :=
  limit (S.fintypeDiagram ⋙ functor c)

def _root_.lightProfiniteToSequential : LightProfinite ⥤ Sequential where
  obj X := Sequential.of X
  map f := ConcreteCategory.ofHom ⟨f, by continuity⟩
  map_id := sorry
  map_comp := sorry

-- This functor should probably be defined as a right Kan extension of the analogous functor to
-- `FintypeCat`, similarly to `Condensed.profiniteSolid`, defined in `Mathlib.Condensed.Solid`.
-- But it will be isomorphic objectwise to `profiniteComponent S c`.
def seqFunctor (S : LightProfinite.{0}) : ℕ+ ⥤ LightProfinite where
  obj c := profiniteComponent S c
  map := sorry
  map_id := sorry
  map_comp := sorry

instance : HasCountableColimits Sequential := sorry

instance : CountableCategory ℕ+ where

def sequential (S : LightProfinite.{0}) : Sequential :=
  colimit (seqFunctor S ⋙ lightProfiniteToSequential)

end FreeImage

end LightProfinite

namespace LightCondAb

variable (S : LightProfinite.{0})

abbrev freeLightProfiniteMap : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ⟶
    sequentialToLightCondSet.obj (lightCondSetToSequential.obj
      ((forget ℤ).obj ((free ℤ).obj S.toCondensed))) :=
  LightCondSet.sequentialAdjunction.unit.app <| (forget ℤ).obj <| (free ℤ).obj S.toCondensed

instance : sequentialToLightCondSet.{0}.Faithful :=
  fullyFaithfulSequentialToLightCondSet.faithful

instance : sequentialToLightCondSet.{0}.Full :=
  fullyFaithfulSequentialToLightCondSet.full

namespace FreeImage

open LightProfinite.FreeImage

def iso : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ≅
    sequentialToLightCondSet.obj (sequential S) := sorry

end FreeImage

instance : IsIso (freeLightProfiniteMap S) := by
  rw [sequentialAdjunction.isIso_unit_app_iff_mem_essImage]
  exact ⟨_, ⟨(FreeImage.iso S).symm⟩⟩

end LightCondAb
