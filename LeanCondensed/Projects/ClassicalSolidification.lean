/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Projects.LightSolid
public import LeanCondensed.Projects.ClassicalSolid

/-!
# Solidification of free light condensed abelian groups

This file identifies the solidification of the free light condensed abelian group `ℤ[S]` with
the independently defined double-dual completed free object `ℤ[S]□`. It also identifies this
solidification with the right-Kan completed free object.
-/

@[expose] public section

noncomputable section

open CategoryTheory LightProfinite MonoidalClosed

namespace LightCondensed
namespace Solid
namespace Classical

/-- The double-dual completed free object is solid. -/
lemma doubleDualFree_obj_isSolid (S : LightProfinite) :
    isSolid (doubleDualFree.obj S) := by
  exact isSolid_internalHom _ _ isSolid_int

/-- The double-dual completed free functor, regarded as a functor to solid light condensed
abelian groups. -/
def doubleDualFreeSolid : LightProfinite ⥤ Solid :=
  isSolid.lift doubleDualFree doubleDualFree_obj_isSolid

/-- Forgetting that the values of `doubleDualFreeSolid` are solid recovers `doubleDualFree`. -/
def doubleDualFreeSolidCompιIso : doubleDualFreeSolid ⋙ isSolid.ι ≅ doubleDualFree :=
  isSolid.liftCompιIso doubleDualFree doubleDualFree_obj_isSolid

set_option backward.isDefEq.respectTransparency false in
/-- Double-dual evaluation with codomain expressed as the underlying object of
`doubleDualFreeSolid`. -/
def doubleDualCompletionSolid :
    lightProfiniteFreeℤ ⟶ doubleDualFreeSolid ⋙ isSolid.ι :=
  doubleDualCompletion ≫ doubleDualFreeSolidCompιIso.inv

set_option backward.isDefEq.respectTransparency false in
/-- The underlying component of `doubleDualCompletionSolid` is double-dual evaluation. -/
@[simp]
lemma doubleDualCompletionSolid_app (S : LightProfinite) :
    doubleDualCompletionSolid.app S = doubleDualCompletion.app S := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The adjoint extension of double-dual evaluation from the solidification of `ℤ[S]` to
`ℤ[S]□`, naturally in `S`. -/
def solidificationFreeToDoubleDual :
    lightProfiniteFreeℤ ⋙ solidification ⟶ doubleDualFreeSolid where
  app S := (solidificationAdjunction.homEquiv
    (lightProfiniteFreeℤ.obj S) (doubleDualFreeSolid.obj S)).symm
      (doubleDualCompletionSolid.app S)
  naturality {S T} f := by
    change solidification.map (lightProfiniteFreeℤ.map f) ≫ _ = _
    rw [← solidificationAdjunction.homEquiv_naturality_left_symm,
      ← solidificationAdjunction.homEquiv_naturality_right_symm]
    congr 1
    exact doubleDualCompletionSolid.naturality f

set_option backward.isDefEq.respectTransparency false in
/-- The component of `solidificationFreeToDoubleDual` is solidification applied to evaluation,
followed by the counit of the solidification adjunction. -/
lemma solidificationFreeToDoubleDual_app (S : LightProfinite) :
    solidificationFreeToDoubleDual.app S =
      solidification.map (doubleDualCompletionSolid.app S) ≫
        solidificationAdjunction.counit.app (doubleDualFreeSolid.obj S) := by
  change (solidificationAdjunction.homEquiv
    (lightProfiniteFreeℤ.obj S) (doubleDualFreeSolid.obj S)).symm
      (doubleDualCompletionSolid.app S) = _
  exact solidificationAdjunction.homEquiv_counit
    (lightProfiniteFreeℤ.obj S) (doubleDualFreeSolid.obj S)
      (doubleDualCompletionSolid.app S)

set_option backward.isDefEq.respectTransparency false in
/-- Every component of the canonical morphism from solidification to the double dual is an
isomorphism. -/
noncomputable instance solidificationFreeToDoubleDual_app_isIso (S : LightProfinite) :
    IsIso (solidificationFreeToDoubleDual.app S) := by
  rw [solidificationFreeToDoubleDual_app]
  haveI : IsIso (solidification.map (doubleDualCompletionSolid.app S)) := by
    rw [doubleDualCompletionSolid_app]
    exact isIso_solidification_map_doubleDualCompletionMap S
  infer_instance

/-- Solidification of the free functor is naturally isomorphic, in `Solid`, to the double-dual
completed free functor. -/
noncomputable def solidificationFreeIsoDoubleDualFreeSolid :
    lightProfiniteFreeℤ ⋙ solidification ≅ doubleDualFreeSolid :=
  NatIso.ofComponents (fun S => asIso (solidificationFreeToDoubleDual.app S)) (by
    intro S T f
    exact solidificationFreeToDoubleDual.naturality f)

/-- The underlying light condensed abelian group of the solidification of `ℤ[S]` is naturally
isomorphic to its double-dual completion `ℤ[S]□`. -/
noncomputable def solidifiedFreeIsoDoubleDualFree :
    lightProfiniteFreeℤ ⋙ solidification ⋙ isSolid.ι ≅ doubleDualFree :=
  Functor.isoWhiskerRight solidificationFreeIsoDoubleDualFreeSolid isSolid.ι ≪≫
    doubleDualFreeSolidCompιIso

/-- Objectwise identification of the solidification of `ℤ[S]` with its double-dual completion
`ℤ[S]□`. -/
noncomputable def solidifiedFreeIsoDoubleDual (S : LightProfinite) :
    (solidification ⋙ isSolid.ι).obj (lightProfiniteFreeℤ.obj S) ≅
      doubleDualCompletedFree S :=
  solidifiedFreeIsoDoubleDualFree.app S

/-- The solidification unit on free light condensed abelian groups. -/
def lightProfiniteFreeSolidificationUnit :
    lightProfiniteFreeℤ ⟶ lightProfiniteFreeℤ ⋙ solidification ⋙ isSolid.ι where
  app S := solidificationAdjunction.unit.app (lightProfiniteFreeℤ.obj S)
  naturality _ _ f := solidificationAdjunction.unit.naturality
    (lightProfiniteFreeℤ.map f)

set_option backward.isDefEq.respectTransparency false in
/-- The solidification unit followed by the comparison with the double dual is evaluation. -/
lemma solidificationUnit_comp_solidifiedFreeIsoDoubleDualFree :
    lightProfiniteFreeSolidificationUnit ≫ solidifiedFreeIsoDoubleDualFree.hom =
      doubleDualCompletion := by
  apply NatTrans.ext
  funext S
  change solidificationAdjunction.unit.app (lightProfiniteFreeℤ.obj S) ≫
      isSolid.ι.map (solidificationFreeToDoubleDual.app S) = doubleDualCompletion.app S
  exact (solidificationAdjunction.homEquiv
    (lightProfiniteFreeℤ.obj S) (doubleDualFreeSolid.obj S)).apply_symm_apply
      (doubleDualCompletion.app S)

/-- Pointwise, the canonical comparison identifies the solidification unit with double-dual
evaluation. -/
@[reassoc]
lemma solidificationUnit_app_comp_solidifiedFreeIsoDoubleDualFree (S : LightProfinite) :
    solidificationAdjunction.unit.app (lightProfiniteFreeℤ.obj S) ≫
        solidifiedFreeIsoDoubleDualFree.hom.app S =
      doubleDualCompletion.app S := by
  exact NatTrans.congr_app solidificationUnit_comp_solidifiedFreeIsoDoubleDualFree S

/-- The solidification of the free functor is naturally isomorphic to the right-Kan completed
free functor. -/
noncomputable def solidifiedFreeIsoClassicalCompletedFree :
    lightProfiniteFreeℤ ⋙ solidification ⋙ isSolid.ι ≅ classicalCompletedFree :=
  solidifiedFreeIsoDoubleDualFree ≪≫ classicalCompletedFreeIsoDoubleDualFree.symm

/-- The solidification unit followed by the comparison with the right-Kan completed free functor
is its canonical completion map. -/
lemma solidificationUnit_comp_solidifiedFreeIsoClassicalCompletedFree :
    lightProfiniteFreeSolidificationUnit ≫
        solidifiedFreeIsoClassicalCompletedFree.hom = classicalCompletion := by
  rw [solidifiedFreeIsoClassicalCompletedFree, Iso.trans_hom]
  rw [← Category.assoc, solidificationUnit_comp_solidifiedFreeIsoDoubleDualFree]
  rw [← classicalCompletion_comp_comparison, Category.assoc]
  simp

/-- Pointwise, the comparison with the right-Kan completed free functor identifies its canonical
completion map with the solidification unit. -/
@[reassoc]
lemma solidificationUnit_app_comp_solidifiedFreeIsoClassicalCompletedFree
    (S : LightProfinite) :
    solidificationAdjunction.unit.app (lightProfiniteFreeℤ.obj S) ≫
        solidifiedFreeIsoClassicalCompletedFree.hom.app S =
      classicalCompletion.app S := by
  exact NatTrans.congr_app
    solidificationUnit_comp_solidifiedFreeIsoClassicalCompletedFree S

end Classical
end Solid
end LightCondensed
