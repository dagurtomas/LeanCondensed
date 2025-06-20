import Mathlib

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  ChosenFiniteProducts Topology

def coprod_desc {n : ℕ} {K : Discrete (Fin n) ⥤ LightProfinite} {c : Cocone K}
    (hc : IsColimit c) (s : Cocone (K ⋙ lightProfiniteToLightCondSet))
  : c.pt.toCondensed ⟶ s.pt := sorry

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet where
  preserves n := {
    preservesColimit {K} := {
      preserves {c} hc := ⟨{
        desc s := coprod_desc hc s
        fac := sorry
        uniq := sorry
      }⟩
    }
  }
