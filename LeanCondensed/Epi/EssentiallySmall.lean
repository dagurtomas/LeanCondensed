/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
/-!

Some missing lemmas about the extensive topology. This has been PRed to mathlib.
-/

open CategoryTheory ConcreteCategory Sheaf Presheaf Category Functor

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable {D : Type*} [Category D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)
variable (A : Type*) [Category A] [ConcreteCategory A]
variable [HasFunctorialSurjectiveInjectiveFactorization A] [K.WEqualsLocallyBijective A]
variable [HasSheafify K A] [K.HasSheafCompose (forget A)] [Balanced (Sheaf K A)]
variable {F G : Sheaf J A} (f : F ⟶ G)
variable [e.TransportsGrothendieckTopology J K]

namespace CategoryTheory.Equivalence

theorem functorPushforward_eq_pullback {U : C} (S : Sieve U) :
    Sieve.functorPushforward e.inverse (Sieve.functorPushforward e.functor S) =
      Sieve.pullback (e.unitInv.app U) S := by
  ext Z f
  rw [← Sieve.functorPushforward_comp]
  simp only [Sieve.functorPushforward_apply, Presieve.functorPushforward, exists_and_left, id_obj,
    comp_obj, Sieve.pullback_apply]
  constructor
  · rintro ⟨W, g, hg, x, rfl⟩
    rw [Category.assoc]
    apply S.downward_closed
    simpa using S.downward_closed hg _
  · intro hf
    exact ⟨_, e.unitInv.app Z ≫ f ≫ e.unitInv.app U, S.downward_closed hf _,
      e.unit.app Z ≫ e.unit.app _, by simp⟩

theorem pullback_functorPushforward_eq {X : C} (S : Sieve X) :
    Sieve.pullback (e.unit.app X) (Sieve.functorPushforward e.inverse
      (Sieve.functorPushforward e.functor S)) = S := by
  ext Z f
  rw [← Sieve.functorPushforward_comp]
  simp only [id_obj, comp_obj, Sieve.pullback_apply, Sieve.functorPushforward_apply,
    Presieve.functorPushforward, Functor.comp_map, inv_fun_map, exists_and_left]
  constructor
  · intro ⟨W, g, hg, x, h⟩
    simp only [← Category.assoc] at h
    change _ ≫ (e.unitIso.app _).hom = _ ≫ (e.unitIso.app _).hom at h
    rw [Iso.cancel_iso_hom_right] at h
    rw [h]
    exact S.downward_closed hg _
  · intro hf
    exact ⟨_, e.unitInv.app Z ≫ f, S.downward_closed hf _, e.unit.app Z ≫ e.unit.app _, by simp⟩

instance : e.symm.TransportsGrothendieckTopology K J where
  eq_inducedTopology := by
    rw [e.eq_inducedTopology_of_transports J K]
    ext X S
    change _ ↔ _ ∈ J.sieves _
    simp only [symm_inverse]
    constructor
    · intro h
      convert J.pullback_stable (e.unitInv.app X) h
      exact e.functorPushforward_eq_pullback S
    · intro h
      convert J.pullback_stable (e.unit.app X) h
      exact (e.pullback_functorPushforward_eq S).symm

lemma isLocallySurjective_iff_epi : IsLocallySurjective f ↔ Epi f := by
  constructor
  · intro
    have := e.hasSheafCompose J K (forget A)
    infer_instance
  · intro h
    rw [← (e.sheafCongr J K A).functor.epi_map_iff_epi, ← isLocallySurjective_iff_epi'] at h
    have : Presheaf.IsLocallySurjective K (whiskerLeft e.inverse.op f.val) := h
    dsimp [Sheaf.IsLocallySurjective]
    apply isLocallySurjective_of_whisker K J e.inverse f.val
    rw [e.symm.eq_inducedTopology_of_transports K J]
    exact e.symm.coverPreserving K

end Equivalence

variable [EssentiallySmall C]
variable [((equivSmallModel C).locallyCoverDense J).inducedTopology.WEqualsLocallyBijective A]
variable [((equivSmallModel C).locallyCoverDense J).inducedTopology.HasSheafCompose (forget A)]
variable [Balanced (Sheaf ((equivSmallModel C).locallyCoverDense J).inducedTopology A)]
variable [HasSheafify ((equivSmallModel C).locallyCoverDense J).inducedTopology A]
variable {F G : Sheaf J A} (f : F ⟶ G)

lemma Sheaf.isLocallySurjective_iff_epi_of_site_essentiallySmall :
    IsLocallySurjective f ↔ Epi f :=
  (equivSmallModel C).isLocallySurjective_iff_epi _
    ((equivSmallModel C).locallyCoverDense J).inducedTopology _ f
