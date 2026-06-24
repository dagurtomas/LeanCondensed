/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Projects.Sequence
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Condensed.Light.InternallyProjective

/-!
# Scaffold for filtered colimits of internal homs out of `P`

This file is a proof scaffold for replacing the remaining `sorry` in
`LightCondensed.Solid.preservesFilteredColimits_ihom_P`.

The planned route is:

1. filtered colimits in `LightCondAb` are computed pointwise;
2. the `T`-valued points of `ihom (P ℤ)` identify with ordinary homs out of
   `P ℤ ⊗ ℤ[T]`;
3. `P ℤ ⊗ ℤ[T]` is a cokernel, so ordinary homs out of it are a finite limit of ordinary
   hom functors out of the numerator and denominator;
4. those numerator/denominator hom functors reduce to point evaluations of filtered colimits.

Most declarations below are intentionally left as `sorry`: the goal is to make the intended Lean
interfaces precise.
-/

noncomputable section

open CategoryTheory LightProfinite Limits LightCondensed MonoidalCategory MonoidalClosed Opposite
open CategoryTheory.Limits

namespace CategoryTheory
namespace Sheaf

variable {C : Type*} [Category C] {D : Type*} [Category D]
variable {J : GrothendieckTopology C} {I : Type*} [Category I]

/-- If presheaf-level colimit cocones of a fixed shape have sheaf colimit points, then the
forgetful functor from sheaves to presheaves creates colimits of that shape. -/
@[implicit_reducible]
noncomputable def createsColimitsOfShapeOfIsSheaf
    (h : ∀ (F : I ⥤ Sheaf J D) (c : Cocone (F ⋙ sheafToPresheaf J D)),
      IsColimit c → Presheaf.IsSheaf J c.pt) :
    CreatesColimitsOfShape I (sheafToPresheaf J D) where
  CreatesColimit {K} := createsColimitOfIsSheaf K (h K)

end Sheaf
end CategoryTheory

namespace LightCondensed
namespace LightSolidFilteredScaffold

/-- Evaluation of a light condensed abelian group at a light profinite set. -/
abbrev lightCondAbPoints (T : LightProfinite) : LightCondAb ⥤ ModuleCat ℤ :=
  sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ) ⋙
    (evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj (Opposite.op T)

/-- The key pointwise-colimit input: a filtered presheaf colimit of light condensed abelian groups
is again a sheaf.

Expected proof: use `LightCondAb.ofSheafLightProfinite`'s explicit criterion, i.e. finite-product
preservation plus the equalizer condition, and the fact that filtered colimits of modules commute
with finite limits. -/
lemma isSheaf_filtered_colimit_presheaf
    {I : Type*} [Category I] [IsFiltered I]
    (F : I ⥤ LightCondAb)
    (c : Cocone (F ⋙ sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)))
    (hc : IsColimit c) :
    Presheaf.IsSheaf (coherentTopology LightProfinite) c.pt := by
  sorry

/-- Filtered colimits of light condensed abelian groups are created by the presheaf-forgetful
functor. -/
@[implicit_reducible]
noncomputable def lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape
    (I : Type*) [Category I] [IsFiltered I] :
    CreatesColimitsOfShape I
      (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ)) :=
  CategoryTheory.Sheaf.createsColimitsOfShapeOfIsSheaf (isSheaf_filtered_colimit_presheaf)

attribute [local instance] lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape

/-- Point evaluation preserves filtered colimits once filtered colimits are pointwise. -/
lemma lightCondAbPoints_preservesFilteredColimits (T : LightProfinite) :
    PreservesFilteredColimits (lightCondAbPoints T) := by
  -- Use the local `CreatesColimitsOfShape` instance above, then the functor-category fact that
  -- evaluation preserves pointwise colimits.
  sorry

/-- Ordinary homs out of a free light condensed module are point evaluations. -/
noncomputable def hom_free_lightProfinite_iso_points (S : LightProfinite) :
    coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj S.toCondensed)) ≅
      lightCondAbPoints S ⋙ CategoryTheory.forget (ModuleCat ℤ) ⋙ uliftFunctor.{1, 0} := by
  -- Combine `freeForgetAdjunction` with `(coherentTopology LightProfinite).yonedaEquiv`.
  sorry

/-- Homs out of a free light condensed module preserve filtered colimits. -/
lemma preservesFilteredColimits_hom_free_lightProfinite (S : LightProfinite) :
    PreservesFilteredColimits
      (coyoneda.obj (Opposite.op ((LightCondensed.free ℤ).obj S.toCondensed))) := by
  -- Transport `lightCondAbPoints_preservesFilteredColimits S` across
  -- `hom_free_lightProfinite_iso_points S`; `forget (ModuleCat ℤ)` and `uliftFunctor` preserve
  -- filtered colimits.
  sorry

/-- Tensor product of free light condensed modules is free on the product. -/
noncomputable def free_tensor_free_iso (S T : LightProfinite) :
    (LightCondensed.free ℤ).obj S.toCondensed ⊗ (LightCondensed.free ℤ).obj T.toCondensed ≅
      (LightCondensed.free ℤ).obj (S ⊗ T).toCondensed := by
  -- This should be the monoidal structure on `LightCondensed.free ℤ`.
  sorry

/-- Homs out of a tensor product of two free light condensed modules preserve filtered colimits. -/
lemma preservesFilteredColimits_hom_free_tensor_free (S T : LightProfinite) :
    PreservesFilteredColimits
      (coyoneda.obj (Opposite.op
        ((LightCondensed.free ℤ).obj S.toCondensed ⊗
          (LightCondensed.free ℤ).obj T.toCondensed))) := by
  -- Transport `preservesFilteredColimits_hom_free_lightProfinite (S ⊗ T)` across
  -- `free_tensor_free_iso S T`.
  sorry

/-- The numerator after tensoring the presentation of `P` with `ℤ[T]`. -/
abbrev PNumeratorTensor (T : LightProfinite) : LightCondAb :=
  ((LightCondensed.free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗
    (LightCondensed.free ℤ).obj T.toCondensed

/-- The denominator after tensoring the presentation of `P` with `ℤ[T]`. -/
abbrev PDenominatorTensor (T : LightProfinite) : LightCondAb :=
  ((LightCondensed.free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed) ⊗
    (LightCondensed.free ℤ).obj T.toCondensed

lemma preservesFilteredColimits_hom_PNumeratorTensor (T : LightProfinite) :
    PreservesFilteredColimits (coyoneda.obj (Opposite.op (PNumeratorTensor T))) := by
  exact preservesFilteredColimits_hom_free_tensor_free _ _

lemma preservesFilteredColimits_hom_PDenominatorTensor (T : LightProfinite) :
    PreservesFilteredColimits (coyoneda.obj (Opposite.op (PDenominatorTensor T))) := by
  exact preservesFilteredColimits_hom_free_tensor_free _ _

-- Local copy of the cokernel/tensor isomorphism, avoiding an import cycle with `LightSolid`.
set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCokerIsoScaffold {A B C : LightCondAb} (f : A ⟶ B) :
    cokernel f ⊗ C ≅ cokernel (f ▷ C) := by
  letI : PreservesColimits (tensorRight C) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight C)
  exact preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

/-- If ordinary homs out of `X` and `Y` preserve filtered colimits, then ordinary homs out of a
cokernel of `X ⟶ Y` preserve filtered colimits.

Expected proof: ordinary hom out of a cokernel is an equalizer of ordinary hom functors, and
filtered colimits commute with finite limits in `Type`. -/
lemma preservesFilteredColimits_hom_cokernel_of_preserves_hom {X Y : LightCondAb} (f : X ⟶ Y)
    [PreservesFilteredColimits (coyoneda.obj (Opposite.op X))]
    [PreservesFilteredColimits (coyoneda.obj (Opposite.op Y))] :
    PreservesFilteredColimits (coyoneda.obj (Opposite.op (cokernel f))) := by
  sorry

/-- Ordinary homs out of `P ℤ ⊗ ℤ[T]` preserve filtered colimits. -/
lemma preservesFilteredColimits_hom_P_tensor_free (T : LightProfinite) :
    PreservesFilteredColimits
      (coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed))) := by
  have hden : PreservesFilteredColimits (coyoneda.obj (Opposite.op (PDenominatorTensor T))) :=
    preservesFilteredColimits_hom_PDenominatorTensor T
  have hnum : PreservesFilteredColimits (coyoneda.obj (Opposite.op (PNumeratorTensor T))) :=
    preservesFilteredColimits_hom_PNumeratorTensor T
  letI : PreservesFilteredColimits (coyoneda.obj (Opposite.op (PDenominatorTensor T))) := hden
  letI : PreservesFilteredColimits (coyoneda.obj (Opposite.op (PNumeratorTensor T))) := hnum
  let f : PDenominatorTensor T ⟶ PNumeratorTensor T :=
    (P_map ℤ) ▷ (LightCondensed.free ℤ).obj T.toCondensed
  have hcoker : PreservesFilteredColimits (coyoneda.obj (Opposite.op (cokernel f))) :=
    preservesFilteredColimits_hom_cokernel_of_preserves_hom f
  -- Transport `hcoker` across `tensorCokerIsoScaffold (P_map ℤ)`.
  sorry

/-- The `T`-valued points of `ihom (P ℤ)` are ordinary homs out of `P ℤ ⊗ ℤ[T]`. -/
noncomputable def ihomP_points_forget_iso (T : LightProfinite) :
    (ihom (P ℤ) ⋙ lightCondAbPoints T ⋙ CategoryTheory.forget (ModuleCat ℤ) ⋙
        uliftFunctor.{1, 0}) ≅
      coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed)) := by
  -- Package `LightCondensed.ihomPoints` as a natural isomorphism of functors.
  sorry

/-- Reduction from pointwise ordinary hom preservation to internal hom preservation. -/
lemma preservesFilteredColimits_ihom_P_of_pointwise_hom
    (h : ∀ T : LightProfinite,
      PreservesFilteredColimits
        (coyoneda.obj (Opposite.op (P ℤ ⊗ (LightCondensed.free ℤ).obj T.toCondensed)))) :
    PreservesFilteredColimits (ihom (P ℤ)) := by
  -- For a filtered diagram, apply `lightCondAb_sheafToPresheaf_createsFilteredColimitsOfShape` and
  -- reflect the target colimit after all `lightCondAbPoints T`; then use
  -- `ihomP_points_forget_iso T` and `h T`.
  sorry

/-- Final scaffold for the target lemma in `LightSolid.lean`. -/
lemma preservesFilteredColimits_ihom_P_scaffold : PreservesFilteredColimits (ihom (P ℤ)) := by
  exact preservesFilteredColimits_ihom_P_of_pointwise_hom
    (fun T => preservesFilteredColimits_hom_P_tensor_free T)

end LightSolidFilteredScaffold
end LightCondensed
