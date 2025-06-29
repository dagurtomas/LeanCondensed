import Mathlib

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  ChosenFiniteProducts Topology

def coprod_desc {n : ℕ} {K : Discrete (Fin n) ⥤ LightProfinite} {c : Cocone K}
    (hc : IsColimit c) (s : Cocone (K ⋙ lightProfiniteToLightCondSet))
  : c.pt.toCondensed ⟶ s.pt :=
    have pres : PreservesFiniteProducts s.pt.val := inferInstance
    let K' := (Discrete.opposite (Fin n)).inverse ⋙ K.op
    let cc := (Cones.whiskeringEquivalence (Discrete.opposite (Fin n)).symm (F := K.op)).functor.obj c.op
    let hcc : IsLimit cc := by apply IsLimit.whiskerEquivalence hc.op
    let scc := s.pt.val.mapCone cc
    let hscc := (pres.preserves n).preservesLimit (K := K').preserves hcc

    let elems : (i : Fin n) → s.pt.val.obj (K'.obj ⟨i⟩) :=
        fun i ↦ (coherentTopology LightProfinite).yonedaEquiv (s.ι.app (Discrete.mk i))
    let lift : s.pt.val.obj cc.pt := sorry
    sorry

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

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{0} where
  preserves _ :=
    preservesShape_fin_of_preserves_binary_and_initial lightProfiniteToLightCondSet _

instance : PreservesColimitsOfShape (Discrete WalkingPair) lightProfiniteToLightCondSet := by
  sorry

instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) lightProfiniteToLightCondSet := by
  sorry

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet where
  preserves n := {
    preservesColimit {K} := {
      preserves {c} hc := by
        apply Nonempty.map isColimitOfOp
        apply coyonedaFunctor_reflectsLimits.reflectsLimitsOfShape.reflectsLimit.reflects
        -- use the coyoneda lemma here
        sorry
    }
  }

instance : PreservesFiniteCoproducts lightProfiniteToLightCondSet.{0} where
  preserves _ :=
    preservesShape_fin_of_preserves_binary_and_initial lightProfiniteToLightCondSet _
