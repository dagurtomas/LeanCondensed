/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Projects.SolidProjectiveGenerator.PBasisTensorDesc
public import LeanCondensed.Projects.SolidProjectiveGenerator.RealQuotient
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.Condensed.Light.AB
public import Mathlib.RingTheory.Flat.CategoryTheory

@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open CategoryTheory.Abelian
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The block index of the dyadic coefficient sequence.  Thus `dyadicBlock n = k` on
`2^k - 1 ≤ n ≤ 2^(k+1) - 2`. -/
def dyadicBlock : ℕ → ℕ
  | 0 => 0
  | n + 1 => dyadicBlock (n / 2) + 1
termination_by n => n

/-- The Camargo dyadic coefficient sequence, constant equal to `2^{-k}` on the `k`th dyadic
block. -/
noncomputable def dyadicCoeff (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ dyadicBlock n

@[simp]
lemma dyadicBlock_zero : dyadicBlock 0 = 0 := by
  rw [dyadicBlock]

@[simp]
lemma dyadicBlock_odd (n : ℕ) : dyadicBlock (2 * n + 1) = dyadicBlock n + 1 := by
  change dyadicBlock (Nat.succ (2 * n)) = dyadicBlock n + 1
  rw [dyadicBlock]
  simp

@[simp]
lemma dyadicBlock_even (n : ℕ) : dyadicBlock (2 * n + 2) = dyadicBlock n + 1 := by
  rw [show 2 * n + 2 = Nat.succ (2 * n + 1) by omega]
  rw [dyadicBlock]
  have h : (2 * n + 1) / 2 = n := by omega
  rw [h]

@[simp]
lemma dyadicCoeff_zero : dyadicCoeff 0 = 1 := by
  simp [dyadicCoeff]

lemma dyadicCoeff_pair_sum (n : ℕ) :
    dyadicCoeff (2 * n + 1) + dyadicCoeff (2 * n + 2) = dyadicCoeff n := by
  simp [dyadicCoeff, pow_succ]
  ring

lemma dyadicBlock_ge_of_ge_two_pow_sub_one (K n : ℕ) (h : 2 ^ K - 1 ≤ n) :
    K ≤ dyadicBlock n := by
  induction K generalizing n with
  | zero => omega
  | succ K ih =>
      cases n with
      | zero =>
          have hp : 1 ≤ 2 ^ (K + 1) - 1 := by
            have hp2 : 2 ≤ 2 ^ (K + 1) := by
              rw [pow_succ']
              have hpos : 1 ≤ 2 ^ K := Nat.one_le_two_pow
              omega
            omega
          omega
      | succ m =>
          rw [dyadicBlock]
          apply Nat.succ_le_succ
          apply ih
          have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ']
          rw [hpow] at h
          have hm : (2 ^ K - 1) * 2 ≤ m := by
            have hpos : 0 < 2 ^ K := Nat.two_pow_pos K
            omega
          exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 hm

lemma tendsto_dyadicBlock_atTop : Filter.Tendsto dyadicBlock Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  refine Filter.eventually_atTop.2 ⟨2 ^ K - 1, ?_⟩
  intro n hn
  exact dyadicBlock_ge_of_ge_two_pow_sub_one K n hn

lemma tendsto_dyadicCoeff_atTop_zero :
    Filter.Tendsto dyadicCoeff Filter.atTop (nhds 0) := by
  unfold dyadicCoeff
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).comp tendsto_dyadicBlock_atTop

namespace LightProfinite

/-- The continuous self-map of `ℕ∪∞` sending `n` to `2n+1` and `∞` to `∞`. -/
def oddMap : ℕ∪{∞} ⟶ ℕ∪{∞} := ConcreteCategory.ofHom {
  toFun
    | ∞ => ∞
    | OnePoint.some n => (2 * n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    let A : Set ℕ := (OnePoint.some ⁻¹' U)ᶜ
    refine ⟨sSup A + 1, fun n hn ↦ by
      have hlt : sSup A < 2 * n + 1 := by omega
      have hnot : 2 * n + 1 ∉ A := notMem_of_csSup_lt hlt (Set.Finite.bddAbove hU)
      simpa [A] using hnot⟩ }

/-- The continuous self-map of `ℕ∪∞` sending `n` to `2n+2` and `∞` to `∞`. -/
def evenMap : ℕ∪{∞} ⟶ ℕ∪{∞} := oddMap ≫ shift

@[simp]
lemma natPoint_comp_oddMap (n : ℕ) :
    natPoint n ≫ oddMap = natPoint (2 * n + 1) := by
  ext x
  rfl

@[simp]
lemma natPoint_comp_evenMap (n : ℕ) :
    natPoint n ≫ evenMap = natPoint (2 * n + 2) := by
  ext x
  rfl

@[simp]
lemma iota_comp_oddMap : ι ≫ oddMap = ι := by
  ext x
  rfl

@[simp]
lemma iota_comp_evenMap : ι ≫ evenMap = ι := by
  ext x
  rfl

@[simp]
lemma oddMap_comp_shift : oddMap ≫ shift = evenMap := rfl

@[simp]
lemma evenMap_comp_shift : evenMap ≫ shift = shift ≫ oddMap := by
  ext x
  cases x using OnePoint.rec <;> rfl

end LightProfinite

/-- The free-object endomorphism induced by `n ↦ 2n+1` on `ℕ∪∞`. -/
noncomputable def freeOddMap :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.oddMap

/-- The free-object endomorphism induced by `n ↦ 2n+2` on `ℕ∪∞`. -/
noncomputable def freeEvenMap :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.evenMap

@[reassoc]
lemma freeNatBasis_comp_freeOddMap (n : ℕ) :
    freeNatBasis n ≫ freeOddMap = freeNatBasis (2 * n + 1) := by
  dsimp [freeNatBasis, freeOddMap]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.oddMap) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint (2 * n + 1)))
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.natPoint_comp_oddMap]

@[reassoc]
lemma freeNatBasis_comp_freeEvenMap (n : ℕ) :
    freeNatBasis n ≫ freeEvenMap = freeNatBasis (2 * n + 2) := by
  dsimp [freeNatBasis, freeEvenMap]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.evenMap) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint (2 * n + 2)))
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.natPoint_comp_evenMap]

@[reassoc]
lemma P_map_comp_freeOddMap : P_map ℤ ≫ freeOddMap = P_map ℤ := by
  dsimp [P_map, freeOddMap]
  change (free ℤ).map (lightProfiniteToLightCondSet.map ι) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.oddMap) =
    (free ℤ).map (lightProfiniteToLightCondSet.map ι)
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.iota_comp_oddMap]

@[reassoc]
lemma P_map_comp_freeEvenMap : P_map ℤ ≫ freeEvenMap = P_map ℤ := by
  dsimp [P_map, freeEvenMap]
  change (free ℤ).map (lightProfiniteToLightCondSet.map ι) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.evenMap) =
    (free ℤ).map (lightProfiniteToLightCondSet.map ι)
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.iota_comp_evenMap]

lemma freeOddMap_comp_shiftFree :
    freeOddMap ≫ (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
      freeEvenMap := by
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.oddMap ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.evenMap
  rw [← Functor.map_comp]
  rw [LightProfinite.oddMap_comp_shift]

lemma freeEvenMap_comp_shiftFree :
    freeEvenMap ≫ (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) ≫ freeOddMap := by
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.evenMap ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.oddMap
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.evenMap_comp_shift]

/-- The `P`-endomorphism extending `[n] ↦ [2n+1]`. -/
noncomputable def pOddMap : P ℤ ⟶ P ℤ :=
  P_homMk ℤ (P ℤ) (freeOddMap ≫ P_proj ℤ) (by
    rw [← Category.assoc, P_map_comp_freeOddMap]
    exact cokernel.condition (P_map ℤ))

/-- The `P`-endomorphism extending `[n] ↦ [2n+2]`. -/
noncomputable def pEvenMap : P ℤ ⟶ P ℤ :=
  P_homMk ℤ (P ℤ) (freeEvenMap ≫ P_proj ℤ) (by
    rw [← Category.assoc, P_map_comp_freeEvenMap]
    exact cokernel.condition (P_map ℤ))

/-- The `P`-endomorphism extending `[n] ↦ [2n+1] + [2n+2]`. -/
noncomputable def pSplitMap : P ℤ ⟶ P ℤ := pOddMap + pEvenMap

@[reassoc]
lemma P_proj_comp_pOddMap : P_proj ℤ ≫ pOddMap = freeOddMap ≫ P_proj ℤ := by
  change cokernel.π (P_map ℤ) ≫ cokernel.desc (P_map ℤ) (freeOddMap ≫ P_proj ℤ) _ = _
  exact cokernel.π_desc (P_map ℤ) (freeOddMap ≫ P_proj ℤ) _

@[reassoc]
lemma P_proj_comp_pEvenMap : P_proj ℤ ≫ pEvenMap = freeEvenMap ≫ P_proj ℤ := by
  change cokernel.π (P_map ℤ) ≫ cokernel.desc (P_map ℤ) (freeEvenMap ≫ P_proj ℤ) _ = _
  exact cokernel.π_desc (P_map ℤ) (freeEvenMap ≫ P_proj ℤ) _

@[reassoc]
lemma P_proj_comp_pSplitMap :
    P_proj ℤ ≫ pSplitMap = (freeOddMap + freeEvenMap) ≫ P_proj ℤ := by
  dsimp [pSplitMap]
  rw [Preadditive.comp_add, P_proj_comp_pOddMap, P_proj_comp_pEvenMap]
  rw [Preadditive.add_comp]

lemma pOddMap_pBasis (n : ℕ) :
    pBasis n ≫ pOddMap = pBasis (2 * n + 1) := by
  dsimp [pBasis]
  calc
    (freeNatBasis n ≫ P_proj ℤ) ≫ pOddMap
        = freeNatBasis n ≫ (P_proj ℤ ≫ pOddMap) := by rw [Category.assoc]
    _ = freeNatBasis n ≫ (freeOddMap ≫ P_proj ℤ) := by rw [P_proj_comp_pOddMap]
    _ = (freeNatBasis n ≫ freeOddMap) ≫ P_proj ℤ := by rw [Category.assoc]
    _ = freeNatBasis (2 * n + 1) ≫ P_proj ℤ := by rw [freeNatBasis_comp_freeOddMap]

lemma pEvenMap_pBasis (n : ℕ) :
    pBasis n ≫ pEvenMap = pBasis (2 * n + 2) := by
  dsimp [pBasis]
  calc
    (freeNatBasis n ≫ P_proj ℤ) ≫ pEvenMap
        = freeNatBasis n ≫ (P_proj ℤ ≫ pEvenMap) := by rw [Category.assoc]
    _ = freeNatBasis n ≫ (freeEvenMap ≫ P_proj ℤ) := by rw [P_proj_comp_pEvenMap]
    _ = (freeNatBasis n ≫ freeEvenMap) ≫ P_proj ℤ := by rw [Category.assoc]
    _ = freeNatBasis (2 * n + 2) ≫ P_proj ℤ := by rw [freeNatBasis_comp_freeEvenMap]

lemma pSplitMap_pBasis (n : ℕ) :
    pBasis n ≫ pSplitMap = pBasis (2 * n + 1) + pBasis (2 * n + 2) := by
  dsimp [pSplitMap]
  rw [Preadditive.comp_add, pOddMap_pBasis, pEvenMap_pBasis]

set_option backward.isDefEq.respectTransparency false in
lemma freeSplitMap_comp_oneMinusShift' :
    (freeOddMap + freeEvenMap) ≫ oneMinusShift' ℤ = oneMinusShift' ℤ ≫ freeOddMap := by
  change (freeOddMap + freeEvenMap) ≫
      (𝟙 ((free ℤ).obj (ℕ∪{∞}).toCondensed) -
        (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift)) =
    (𝟙 ((free ℤ).obj (ℕ∪{∞}).toCondensed) -
        (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift)) ≫ freeOddMap
  rw [Preadditive.add_comp]
  rw [Preadditive.comp_sub, Preadditive.comp_sub, Preadditive.sub_comp]
  rw [Category.comp_id, Category.comp_id, Category.id_comp]
  rw [freeOddMap_comp_shiftFree, freeEvenMap_comp_shiftFree]
  abel

lemma pSplitMap_comp_oneMinusShift :
    pSplitMap ≫ oneMinusShift ℤ = oneMinusShift ℤ ≫ pOddMap := by
  haveI : Epi (P_proj ℤ) := by
    change Epi (cokernel.π (P_map ℤ))
    infer_instance
  apply (cancel_epi (P_proj ℤ)).1
  calc
    P_proj ℤ ≫ pSplitMap ≫ oneMinusShift ℤ
        = (freeOddMap + freeEvenMap) ≫ P_proj ℤ ≫ oneMinusShift ℤ := by
          simpa [Category.assoc] using
            congrArg (fun f => f ≫ oneMinusShift ℤ) P_proj_comp_pSplitMap
    _ = (freeOddMap + freeEvenMap) ≫ oneMinusShift' ℤ ≫ P_proj ℤ := by
          simpa [Category.assoc] using
            congrArg (fun f => (freeOddMap + freeEvenMap) ≫ f) P_proj_oneMinusShift
    _ = oneMinusShift' ℤ ≫ freeOddMap ≫ P_proj ℤ := by
          simpa [Category.assoc] using
            congrArg (fun f => f ≫ P_proj ℤ) freeSplitMap_comp_oneMinusShift'
    _ = oneMinusShift' ℤ ≫ P_proj ℤ ≫ pOddMap := by
          simpa [Category.assoc] using
            congrArg (fun f => oneMinusShift' ℤ ≫ f) P_proj_comp_pOddMap.symm
    _ = P_proj ℤ ≫ oneMinusShift ℤ ≫ pOddMap := by
          simpa [Category.assoc] using
            congrArg (fun f => f ≫ pOddMap) P_proj_oneMinusShift.symm

abbrev lightCondAbPresheaf := LightProfinite.{0}ᵒᵖ ⥤ ModuleCat.{0} ℤ

lemma presheaf_freeTensor_preservesFiniteLimits (X : LightProfinite.{0}) :
    PreservesFiniteLimits (tensorLeft (X.toCondensed.obj ⋙ ModuleCat.free ℤ : lightCondAbPresheaf)) := by
  apply preservesFiniteLimits_of_evaluation
  intro S
  have hflat : Module.Flat ℤ ((X.toCondensed.obj ⋙ ModuleCat.free ℤ : lightCondAbPresheaf).obj S) := by
    change Module.Flat ℤ (X.toCondensed.obj.obj S →₀ ℤ)
    infer_instance
  letI := hflat
  exact preservesFiniteLimits_of_natIso
    (F := ((evaluation LightProfinite.{0}ᵒᵖ (ModuleCat.{0} ℤ)).obj S ⋙
      tensorLeft ((X.toCondensed.obj ⋙ ModuleCat.free ℤ : lightCondAbPresheaf).obj S)))
    (G := (tensorLeft (X.toCondensed.obj ⋙ ModuleCat.free ℤ : lightCondAbPresheaf) ⋙
      (evaluation LightProfinite.{0}ᵒᵖ (ModuleCat.{0} ℤ)).obj S))
    (by
      refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
      intro _ _ f
      ext x
      rfl)

/-- The functor obtained by tensoring the underlying presheaf with the free presheaf on `X`, then
sheafifying.  This is naturally isomorphic to sheaf-level tensoring by `ℤ[X]`. -/
noncomputable def freePresheafTensorFunctor (X : LightProfinite.{0}) : LightCondAb ⥤ LightCondAb :=
  sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ) ⋙
    tensorLeft (X.toCondensed.obj ⋙ ModuleCat.free ℤ : lightCondAbPresheaf) ⋙
      presheafToSheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)

set_option synthInstance.maxHeartbeats 120000 in
lemma freePresheafTensorFunctor_preservesFiniteLimits (X : LightProfinite.{0}) :
    PreservesFiniteLimits (freePresheafTensorFunctor X) := by
  let F : lightCondAbPresheaf := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  haveI : PreservesFiniteLimits (tensorLeft F) := presheaf_freeTensor_preservesFiniteLimits X
  haveI : PreservesFiniteLimits
      (sheafToPresheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)) := inferInstance
  haveI : PreservesFiniteLimits
      (presheafToSheaf (coherentTopology LightProfinite.{0}) (ModuleCat.{0} ℤ)) := inferInstance
  dsimp [freePresheafTensorFunctor, F]
  infer_instance

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 120000 in
noncomputable def freeTensorFunctorIsoApp (X : LightProfinite.{0}) (B : LightCondAb) :
    (tensorLeft ((free ℤ).obj X.toCondensed)).obj B ≅ (freePresheafTensorFunctor X).obj B := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : lightCondAbPresheaf := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let cB : L.obj B.obj ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  haveI : IsIso cB := by
    dsimp [cB, L]
    exact isIso_sheafificationAdjunction_counit B
  dsimp [freePresheafTensorFunctor, tensorLeft, LightCondensed.free, Sheaf.composeAndSheafify]
  change L.obj F ⊗ B ≅ L.obj (F ⊗ B.obj)
  exact (Iso.refl (L.obj F) ⊗ᵢ (asIso cB).symm) ≪≫ Functor.Monoidal.μIso L F B.obj

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 120000 in
lemma freeTensorFunctorIsoApp_hom_naturality (X : LightProfinite.{0}) {B C : LightCondAb}
    (f : B ⟶ C) :
    (freeTensorFunctorIsoApp X B).hom ≫ (freePresheafTensorFunctor X).map f =
      (tensorLeft ((free ℤ).obj X.toCondensed)).map f ≫ (freeTensorFunctorIsoApp X C).hom := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let F : lightCondAbPresheaf := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let cB : L.obj B.obj ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let cC : L.obj C.obj ⟶ C :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app C
  haveI : IsIso cB := by
    dsimp [cB, L]
    exact isIso_sheafificationAdjunction_counit B
  haveI : IsIso cC := by
    dsimp [cC, L]
    exact isIso_sheafificationAdjunction_counit C
  dsimp [freeTensorFunctorIsoApp]
  dsimp [freePresheafTensorFunctor, tensorLeft, LightCondensed.free, Sheaf.composeAndSheafify]
  change ((Iso.refl (L.obj F) ⊗ᵢ (asIso cB).symm) ≪≫ Functor.Monoidal.μIso L F B.obj).hom ≫
      L.map (F ◁ f.hom) =
    (L.obj F ◁ f) ≫
      (((Iso.refl (L.obj F) ⊗ᵢ (asIso cC).symm) ≪≫ Functor.Monoidal.μIso L F C.obj).hom)
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
    Functor.Monoidal.μIso_hom, Category.assoc]
  slice_lhs 2 3 => rw [← Functor.LaxMonoidal.μ_natural_right L F f.hom]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hc : cB ≫ f = L.map f.hom ≫ cC := by
    dsimp [cB, cC]
    exact ((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.naturality f).symm
  have hinv : inv cB ≫ L.map f.hom = f ≫ inv cC := by
    rw [← cancel_mono cC]
    simp [Category.assoc, hc]
  have hinv' : (asIso cB).symm.hom ≫ L.map f.hom = f ≫ (asIso cC).symm.hom := by
    simpa using hinv
  rw [hinv']
  rw [MonoidalCategory.whiskerLeft_comp_assoc]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- Tensoring by a free light condensed abelian group is the sheafification of objectwise tensoring
by the corresponding free presheaf. -/
noncomputable def freeTensorFunctorIso (X : LightProfinite.{0}) :
    tensorLeft ((free ℤ).obj X.toCondensed) ≅ freePresheafTensorFunctor X :=
  NatIso.ofComponents (fun B => freeTensorFunctorIsoApp X B)
    (fun f => (freeTensorFunctorIsoApp_hom_naturality X f).symm)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 120000 in
lemma tensorLeft_free_preservesFiniteLimits (X : LightProfinite.{0}) :
    PreservesFiniteLimits (tensorLeft ((free ℤ).obj X.toCondensed)) := by
  haveI : PreservesFiniteLimits (freePresheafTensorFunctor X) :=
    freePresheafTensorFunctor_preservesFiniteLimits X
  exact preservesFiniteLimits_of_natIso (freeTensorFunctorIso X).symm

/-- `tensorLeft (P ℤ)` is a functor retract of tensoring by the free sheaf on `ℕ∪{∞}`. -/
noncomputable def tensorLeftP_retract_tensorLeftFreeNinf :
    Retract (tensorLeft (P ℤ)) (tensorLeft ((free ℤ).obj (ℕ∪{∞}).toCondensed)) where
  i := {
    app X := (P_retract ℤ).i ▷ X
    naturality X Y f := by
      change (P ℤ ◁ f) ≫ ((P_retract ℤ).i ▷ Y) =
        ((P_retract ℤ).i ▷ X) ≫ ((free ℤ).obj (ℕ∪{∞}).toCondensed ◁ f)
      rw [whisker_exchange] }
  r := {
    app X := (P_retract ℤ).r ▷ X
    naturality X Y f := by
      change ((free ℤ).obj (ℕ∪{∞}).toCondensed ◁ f) ≫ ((P_retract ℤ).r ▷ Y) =
        ((P_retract ℤ).r ▷ X) ≫ (P ℤ ◁ f)
      rw [whisker_exchange] }
  retract := by
    apply NatTrans.ext
    funext X
    change ((P_retract ℤ).i ▷ X) ≫ ((P_retract ℤ).r ▷ X) = 𝟙 (P ℤ ⊗ X)
    rw [← comp_whiskerRight, (P_retract ℤ).retract]
    simp

set_option maxHeartbeats 1000000 in
instance tensorLeft_P_preservesMonomorphisms : (tensorLeft (P ℤ)).PreservesMonomorphisms := by
  haveI : PreservesFiniteLimits (tensorLeft ((free ℤ).obj (ℕ∪{∞}).toCondensed)) :=
    tensorLeft_free_preservesFiniteLimits (ℕ∪{∞})
  haveI : (tensorLeft ((free ℤ).obj (ℕ∪{∞}).toCondensed)).PreservesMonomorphisms :=
    inferInstance
  exact CategoryTheory.Functor.preservesMonomorphisms.ofRetract tensorLeftP_retract_tensorLeftFreeNinf

/-- Since `tensorLeft (P ℤ)` preserves monomorphisms, its right adjoint preserves injectives. -/
instance ihom_P_preservesInjectiveObjects : (ihom (P ℤ)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (ihom.adjunction (P ℤ))

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero solidity for `(oneMinusShift ℤ) ▷ X`, stated before passing to `Ext⁰`.

Under the closed monoidal adjunction, precomposition by `(oneMinusShift ℤ) ▷ X` is
postcomposition by the solid isomorphism
`(MonoidalClosed.pre (oneMinusShift ℤ)).app ((isSolid.ι).obj E)`. -/
lemma hom_precomp_oneMinusShift_tensor_bijective
    (X : LightCondAb) (E : Solid) :
    Function.Bijective
      (fun f : P ℤ ⊗ X ⟶ (isSolid.ι).obj E => ((oneMinusShift ℤ) ▷ X) ≫ f) := by
  let φ := (MonoidalClosed.pre (oneMinusShift ℤ)).app ((isSolid.ι).obj E)
  haveI : IsIso φ := E.property
  have hcompat : ∀ f : P ℤ ⊗ X ⟶ (isSolid.ι).obj E,
      MonoidalClosed.curry (((oneMinusShift ℤ) ▷ X) ≫ f) =
        MonoidalClosed.curry f ≫ φ := by
    intro f
    dsimp [φ]
    rw [MonoidalClosed.curry_pre_app]
  constructor
  · intro f g hfg
    apply MonoidalClosed.curry_injective
    apply (cancel_mono φ).1
    rw [← hcompat f, ← hcompat g]
    exact congrArg MonoidalClosed.curry hfg
  · intro g
    let a : X ⟶ (ihom (P ℤ)).obj ((isSolid.ι).obj E) := MonoidalClosed.curry g ≫ inv φ
    refine ⟨MonoidalClosed.uncurry a, ?_⟩
    apply MonoidalClosed.curry_injective
    rw [hcompat]
    dsimp [a, φ]
    simp

attribute [local instance] CategoryTheory.HasExt.standard

/-- The SPG12b statement in degree `0`: precomposition by `(oneMinusShift ℤ) ▷ X` is
bijective on `Ext⁰`, equivalently on ordinary Homs. -/
lemma ext0_precomp_oneMinusShift_tensor_bijective
    (X : LightCondAb) (E : Solid) :
    Function.Bijective
      (fun α : CategoryTheory.Abelian.Ext (P ℤ ⊗ X) ((isSolid.ι).obj E) 0 =>
        (CategoryTheory.Abelian.Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp α (zero_add 0)) := by
  have hhom := hom_precomp_oneMinusShift_tensor_bijective X E
  constructor
  · intro α β hαβ
    rcases (CategoryTheory.Abelian.Ext.mk₀_bijective (P ℤ ⊗ X) ((isSolid.ι).obj E)).2 α
      with ⟨f, rfl⟩
    rcases (CategoryTheory.Abelian.Ext.mk₀_bijective (P ℤ ⊗ X) ((isSolid.ι).obj E)).2 β
      with ⟨g, rfl⟩
    simp only [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀] at hαβ ⊢
    apply congrArg CategoryTheory.Abelian.Ext.mk₀
    exact hhom.1 ((CategoryTheory.Abelian.Ext.mk₀_bijective _ _).1 hαβ)
  · intro α
    rcases (CategoryTheory.Abelian.Ext.mk₀_bijective (P ℤ ⊗ X) ((isSolid.ι).obj E)).2 α
      with ⟨g, rfl⟩
    rcases hhom.2 g with ⟨f, hf⟩
    refine ⟨CategoryTheory.Abelian.Ext.mk₀ f, ?_⟩
    simp only [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg CategoryTheory.Abelian.Ext.mk₀ hf


namespace ExtOne

lemma precomp_delta {A B : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) (σ : A ⟶ B) (q : B ⟶ S.X₃) :
    (Ext.mk₀ σ).comp ((Ext.mk₀ q).comp hS.extClass (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ (σ ≫ q)).comp hS.extClass (zero_add 1) := by
  rw [← Ext.comp_assoc_of_second_deg_zero (Ext.mk₀ σ) (Ext.mk₀ q) hS.extClass (zero_add 1)]
  rw [Ext.mk₀_comp_mk₀]

lemma delta_zero_iff {A : LightCondAb} {S : ShortComplex LightCondAb} (hS : S.ShortExact)
    (q : A ⟶ S.X₃) :
    (Ext.mk₀ q).comp hS.extClass (zero_add 1) = 0 ↔
      ∃ p : A ⟶ S.X₂, p ≫ S.g = q := by
  constructor
  · intro hq
    rcases Ext.covariant_sequence_exact₃ A hS (Ext.mk₀ q) (rfl : 0 + 1 = 1) hq with ⟨x₂, hx₂⟩
    rcases (Ext.mk₀_bijective A S.X₂).2 x₂ with ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    simp only [Ext.mk₀_comp_mk₀] at hx₂
    exact (Ext.mk₀_bijective A S.X₃).1 hx₂
  · rintro ⟨p, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    rw [Ext.comp_assoc_of_second_deg_zero]
    simp

lemma delta_surjective_of_injective_middle {A : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) [Injective S.X₂] (α : Ext A S.X₁ 1) :
    ∃ q : A ⟶ S.X₃, (Ext.mk₀ q).comp hS.extClass (zero_add 1) = α := by
  have hzero : α.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
    haveI : Subsingleton (Ext A S.X₂ 1) := Ext.subsingleton_of_injective A S.X₂ 0
    exact Subsingleton.elim _ _
  rcases Ext.covariant_sequence_exact₁ A hS α hzero (rfl : 0 + 1 = 1) with ⟨x₃, hx₃⟩
  rcases (Ext.mk₀_bijective A S.X₃).2 x₃ with ⟨q, rfl⟩
  exact ⟨q, hx₃⟩

lemma delta_eq_of_delta_sub_eq_zero {A : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) {q c : A ⟶ S.X₃}
    (h : (Ext.mk₀ (q - c)).comp hS.extClass (zero_add 1) = 0) :
    (Ext.mk₀ q).comp hS.extClass (zero_add 1) =
      (Ext.mk₀ c).comp hS.extClass (zero_add 1) := by
  have hqc : q = c + (q - c) := by abel
  rw [hqc, Ext.mk₀_add, Ext.add_comp, h]
  simp

lemma curry_delta_zero_iff {X : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) (q : P ℤ ⊗ X ⟶ S.X₃) :
    (Ext.mk₀ (MonoidalClosed.curry q)).comp
        (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) = 0 ↔
      (Ext.mk₀ q).comp hS.extClass (zero_add 1) = 0 := by
  constructor
  · intro hG
    rcases (delta_zero_iff (A := X) (hS.map_of_exact (ihom (P ℤ))) (MonoidalClosed.curry q)).1 hG with
      ⟨pG, hpG⟩
    refine (delta_zero_iff hS q).2 ⟨MonoidalClosed.uncurry pG, ?_⟩
    apply MonoidalClosed.curry_injective
    rw [MonoidalClosed.curry_natural_right]
    rw [MonoidalClosed.curry_uncurry]
    change pG ≫ (ihom (P ℤ)).map S.g = MonoidalClosed.curry q at hpG
    exact hpG
  · intro hF
    rcases (delta_zero_iff hS q).1 hF with ⟨p, hp⟩
    refine (delta_zero_iff (A := X) (hS.map_of_exact (ihom (P ℤ))) (MonoidalClosed.curry q)).2
      ⟨MonoidalClosed.curry p, ?_⟩
    change MonoidalClosed.curry p ≫ (ihom (P ℤ)).map S.g = MonoidalClosed.curry q
    rw [← MonoidalClosed.curry_natural_right]
    rw [hp]

noncomputable def ihomOneMinusShiftShortComplexHom (S : ShortComplex LightCondAb) :
    (S.map (ihom (P ℤ))).Hom (S.map (ihom (P ℤ))) :=
  ShortComplex.Hom.mk
    ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₁)
    ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₂)
    ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃)
    (by
      change ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₁) ≫ (ihom (P ℤ)).map S.f =
        (ihom (P ℤ)).map S.f ≫ ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₂)
      exact ((MonoidalClosed.pre (oneMinusShift ℤ)).naturality S.f).symm)
    (by
      change ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₂) ≫ (ihom (P ℤ)).map S.g =
        (ihom (P ℤ)).map S.g ≫ ((MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃)
      exact ((MonoidalClosed.pre (oneMinusShift ℤ)).naturality S.g).symm)

lemma delta_comp_ihomOneMinusShift {X : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) (d : X ⟶ (S.map (ihom (P ℤ))).X₃) :
    (Ext.mk₀ (d ≫ (ihomOneMinusShiftShortComplexHom S).τ₃)).comp
        (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) =
      ((Ext.mk₀ d).comp (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1)).comp
        (Ext.mk₀ (ihomOneMinusShiftShortComplexHom S).τ₁) (add_zero 1) := by
  let hGS := hS.map_of_exact (ihom (P ℤ))
  let φS := ihomOneMinusShiftShortComplexHom S
  have hnat := ShortComplex.ShortExact.extClass_naturality hGS hGS φS
  rw [Ext.comp_assoc_of_third_deg_zero]
  rw [hnat]
  rw [← Ext.comp_assoc_of_second_deg_zero (Ext.mk₀ d) (Ext.mk₀ φS.τ₃) hGS.extClass (zero_add 1)]
  rw [Ext.mk₀_comp_mk₀]

lemma delta_zero_of_curry_delta_zero {X : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) {q : P ℤ ⊗ X ⟶ S.X₃}
    (hG : (Ext.mk₀ (MonoidalClosed.curry q)).comp
        (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) = 0) :
    (Ext.mk₀ q).comp hS.extClass (zero_add 1) = 0 :=
  (curry_delta_zero_iff hS q).1 hG

lemma delta_eq_iff_curry_delta_eq {X : LightCondAb} {S : ShortComplex LightCondAb}
    (hS : S.ShortExact) (q r : P ℤ ⊗ X ⟶ S.X₃) :
    (Ext.mk₀ q).comp hS.extClass (zero_add 1) =
        (Ext.mk₀ r).comp hS.extClass (zero_add 1) ↔
      (Ext.mk₀ (MonoidalClosed.curry q)).comp
          (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) =
        (Ext.mk₀ (MonoidalClosed.curry r)).comp
          (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) := by
  constructor
  · intro h
    have hzero : (Ext.mk₀ (q - r)).comp hS.extClass (zero_add 1) = 0 := by
      rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp, h]
      simp
    have hGzero := (curry_delta_zero_iff hS (q - r)).2 hzero
    have hcurry_sub : MonoidalClosed.curry (q - r) =
        MonoidalClosed.curry q - MonoidalClosed.curry r := by
      change (ihom.adjunction (P ℤ)).homEquiv X S.X₃ (q - r) =
        (ihom.adjunction (P ℤ)).homEquiv X S.X₃ q -
          (ihom.adjunction (P ℤ)).homEquiv X S.X₃ r
      exact Adjunction.homAddEquiv_sub (ihom.adjunction (P ℤ)) X S.X₃ q r
    rw [hcurry_sub, sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp] at hGzero
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hGzero)
  · intro h
    have hGzero : (Ext.mk₀ (MonoidalClosed.curry (q - r))).comp
          (hS.map_of_exact (ihom (P ℤ))).extClass (zero_add 1) = 0 := by
      have hcurry_sub : MonoidalClosed.curry (q - r) =
          MonoidalClosed.curry q - MonoidalClosed.curry r := by
        change (ihom.adjunction (P ℤ)).homEquiv X S.X₃ (q - r) =
          (ihom.adjunction (P ℤ)).homEquiv X S.X₃ q -
            (ihom.adjunction (P ℤ)).homEquiv X S.X₃ r
        exact Adjunction.homAddEquiv_sub (ihom.adjunction (P ℤ)) X S.X₃ q r
      rw [hcurry_sub, sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp, h]
      simp
    have hzero := (curry_delta_zero_iff hS (q - r)).1 hGzero
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp] at hzero
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hzero)

set_option backward.isDefEq.respectTransparency false in
lemma ext1_precomp_oneMinusShift_tensor_bijective
    (X : LightCondAb) (E : Solid) :
    Function.Bijective
      (fun α : Ext (P ℤ ⊗ X) ((isSolid.ι).obj E) 1 =>
        (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp α (zero_add 1)) := by
  let Y : LightCondAb := (isSolid.ι).obj E
  let φY := (MonoidalClosed.pre (oneMinusShift ℤ)).app Y
  letI : IsIso φY := E.property
  let ip := (EnoughInjectives.presentation Y).some
  let S := ip.shortComplex
  have hS : S.ShortExact := ip.shortExact_shortComplex
  haveI : Injective S.X₂ := by
    dsimp [S, InjectivePresentation.shortComplex]
    exact ip.injective
  let hGS := hS.map_of_exact (ihom (P ℤ))
  haveI : Injective (S.map (ihom (P ℤ))).X₂ := by
    change Injective ((ihom (P ℤ)).obj S.X₂)
    exact Functor.PreservesInjectiveObjects.injective_obj (F := ihom (P ℤ)) (X := S.X₂) inferInstance
  let φS := ihomOneMinusShiftShortComplexHom S
  have hφY : φS.τ₁ = φY := by
    rfl
  haveI : IsIso φS.τ₁ := by
    rw [hφY]
    dsimp [φY, Y]
    exact E.property
  constructor
  · intro α β hαβ
    rcases delta_surjective_of_injective_middle hS α with ⟨q, hq⟩
    rcases delta_surjective_of_injective_middle hS β with ⟨r, hr⟩
    rw [← hq, ← hr]
    apply delta_eq_of_delta_sub_eq_zero hS
    have hαβ' :
        (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp
            ((Ext.mk₀ q).comp hS.extClass (zero_add 1)) (zero_add 1) =
          (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp
            ((Ext.mk₀ r).comp hS.extClass (zero_add 1)) (zero_add 1) := by
      rw [hq, hr]
      exact hαβ
    have hσeq :
        (Ext.mk₀ (((oneMinusShift ℤ) ▷ X) ≫ q)).comp hS.extClass (zero_add 1) =
          (Ext.mk₀ (((oneMinusShift ℤ) ▷ X) ≫ r)).comp hS.extClass (zero_add 1) := by
      simpa [precomp_delta hS ((oneMinusShift ℤ) ▷ X) q,
        precomp_delta hS ((oneMinusShift ℤ) ▷ X) r] using hαβ'
    have hσzero :
        (Ext.mk₀ (((oneMinusShift ℤ) ▷ X) ≫ (q - r))).comp hS.extClass (zero_add 1) = 0 := by
      rw [Preadditive.comp_sub, sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg,
        Ext.add_comp, Ext.neg_comp, hσeq]
      simp
    have hGσzero := (curry_delta_zero_iff hS (((oneMinusShift ℤ) ▷ X) ≫ (q - r))).2 hσzero
    have hcurryσ : MonoidalClosed.curry (((oneMinusShift ℤ) ▷ X) ≫ (q - r)) =
        MonoidalClosed.curry (q - r) ≫ (MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃ := by
      rw [MonoidalClosed.curry_pre_app]
    rw [hcurryσ] at hGσzero
    let dqr : X ⟶ (S.map (ihom (P ℤ))).X₃ := MonoidalClosed.curry (q - r)
    change (Ext.mk₀ (dqr ≫ φS.τ₃)).comp hGS.extClass (zero_add 1) = 0 at hGσzero
    have hδφ := delta_comp_ihomOneMinusShift hS (d := dqr)
    rw [hδφ] at hGσzero
    change ((Ext.mk₀ dqr).comp hGS.extClass (zero_add 1)).comp
      (Ext.mk₀ φS.τ₁) (add_zero 1) = 0 at hGσzero
    have hGzero : (Ext.mk₀ (MonoidalClosed.curry (q - r))).comp hGS.extClass (zero_add 1) = 0 := by
      change (Ext.mk₀ dqr).comp hGS.extClass (zero_add 1) = 0
      have htmp := congrArg (fun z => z.comp (Ext.mk₀ (inv φS.τ₁)) (add_zero 1)) hGσzero
      simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
        IsIso.hom_inv_id, Ext.comp_mk₀_id, Ext.zero_comp] using htmp
    exact (curry_delta_zero_iff hS (q - r)).1 hGzero
  · intro α
    rcases delta_surjective_of_injective_middle hS α with ⟨q, hq⟩
    let δGq : Ext X (S.map (ihom (P ℤ))).X₁ 1 :=
      (Ext.mk₀ (MonoidalClosed.curry q)).comp hGS.extClass (zero_add 1)
    let γ : Ext X (S.map (ihom (P ℤ))).X₁ 1 :=
      δGq.comp (Ext.mk₀ (inv φS.τ₁)) (add_zero 1)
    rcases delta_surjective_of_injective_middle hGS γ with ⟨d, hd⟩
    let d' : X ⟶ (ihom (P ℤ)).obj S.X₃ := d
    let q' : P ℤ ⊗ X ⟶ S.X₃ := MonoidalClosed.uncurry d'
    refine ⟨(Ext.mk₀ q').comp hS.extClass (zero_add 1), ?_⟩
    change (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp
        ((Ext.mk₀ q').comp hS.extClass (zero_add 1)) (zero_add 1) = α
    rw [precomp_delta hS ((oneMinusShift ℤ) ▷ X) q']
    rw [← hq]
    apply (delta_eq_iff_curry_delta_eq hS (((oneMinusShift ℤ) ▷ X) ≫ q') q).2
    have hcurryσ : MonoidalClosed.curry (((oneMinusShift ℤ) ▷ X) ≫ q') =
        d' ≫ (MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃ := by
      dsimp [q']
      calc
        MonoidalClosed.curry (((oneMinusShift ℤ) ▷ X) ≫ MonoidalClosed.uncurry d') =
            MonoidalClosed.curry (MonoidalClosed.uncurry d') ≫
              (MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃ :=
          (MonoidalClosed.curry_pre_app (oneMinusShift ℤ) (MonoidalClosed.uncurry d')).symm
        _ = d' ≫ (MonoidalClosed.pre (oneMinusShift ℤ)).app S.X₃ := by
          rw [MonoidalClosed.curry_uncurry]
    rw [hcurryσ]
    change (Ext.mk₀ (d ≫ φS.τ₃)).comp hGS.extClass (zero_add 1) =
      (Ext.mk₀ (MonoidalClosed.curry q)).comp hGS.extClass (zero_add 1)
    have hδφ := delta_comp_ihomOneMinusShift hS (d := d)
    rw [hδφ, hd]
    change (δGq.comp (Ext.mk₀ (inv φS.τ₁)) (add_zero 1)).comp
      (Ext.mk₀ φS.τ₁) (add_zero 1) = δGq
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      IsIso.inv_hom_id, Ext.comp_mk₀_id]

end ExtOne

/-- The SPG12b statement in degree `1`: precomposition by `(oneMinusShift ℤ) ▷ X` is
bijective on `Ext¹` for every solid target. -/
lemma ext1_precomp_oneMinusShift_tensor_bijective
    (X : LightCondAb) (E : Solid) :
    Function.Bijective
      (fun α : Ext (P ℤ ⊗ X) ((isSolid.ι).obj E) 1 =>
        (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp α (zero_add 1)) :=
  ExtOne.ext1_precomp_oneMinusShift_tensor_bijective X E

/-- The finite `P`-basis slice of `P ℤ ⊗ X` at `n`. -/
noncomputable def pBasisTensorSlice (X : LightCondAb) (n : ℕ) : X ⟶ P ℤ ⊗ X :=
  (λ_ X).inv ≫ pBasis n ▷ X

lemma pBasis_comp_oneMinusShift (n : ℕ) :
    pBasis n ≫ oneMinusShift ℤ = pBasis n - pBasis (n + 1) := by
  dsimp [pBasis]
  calc
    (freeNatBasis n ≫ P_proj ℤ) ≫ oneMinusShift ℤ
        = freeNatBasis n ≫ (P_proj ℤ ≫ oneMinusShift ℤ) := by rw [Category.assoc]
    _ = freeNatBasis n ≫ (oneMinusShift' ℤ ≫ P_proj ℤ) := by rw [P_proj_oneMinusShift]
    _ = (freeNatBasis n ≫ oneMinusShift' ℤ) ≫ P_proj ℤ := by rw [Category.assoc]
    _ = (freeNatBasis n - freeNatBasis (n + 1)) ≫ P_proj ℤ := by
          rw [freeNatBasis_oneMinusShift']
    _ = freeNatBasis n ≫ P_proj ℤ - freeNatBasis (n + 1) ≫ P_proj ℤ := by
          rw [Preadditive.sub_comp]

/-- Slicing after precomposition by `(oneMinusShift ℤ) ▷ X` takes the finite difference of
adjacent finite `P`-slices. -/
lemma pBasisTensorSlice_comp_oneMinusShift (X : LightCondAb) (n : ℕ) :
    pBasisTensorSlice X n ≫ ((oneMinusShift ℤ) ▷ X) =
      pBasisTensorSlice X n - pBasisTensorSlice X (n + 1) := by
  simpa only [pBasisTensorSlice, comp_whiskerRight, IntProof.sub_whiskerRight,
    Preadditive.comp_sub, Category.assoc] using
      congrArg (fun f : 𝟙_ LightCondAb ⟶ P ℤ => (λ_ X).inv ≫ f ▷ X)
        (pBasis_comp_oneMinusShift n)

/-- The odd map sends the `n`th finite tensor slice to the `(2n+1)`st slice. -/
lemma pBasisTensorSlice_comp_pOddMap (X : LightCondAb) (n : ℕ) :
    pBasisTensorSlice X n ≫ (pOddMap ▷ X) = pBasisTensorSlice X (2 * n + 1) := by
  simpa only [pBasisTensorSlice, comp_whiskerRight, Category.assoc] using
    congrArg (fun f : 𝟙_ LightCondAb ⟶ P ℤ => (λ_ X).inv ≫ f ▷ X)
      (pOddMap_pBasis n)

/-- The `F/G` identity after tensoring on the right by `X`. -/
lemma pSplitMap_tensor_comp_oneMinusShift_tensor (X : LightCondAb) :
    (pSplitMap ▷ X) ≫ ((oneMinusShift ℤ) ▷ X) =
      ((oneMinusShift ℤ) ▷ X) ≫ (pOddMap ▷ X) := by
  simpa only [comp_whiskerRight] using
    congrArg (fun f => f ▷ X) pSplitMap_comp_oneMinusShift

private lemma ext_mk₀_sub {A B : LightCondAb} (f g : A ⟶ B) :
    Ext.mk₀ (f - g) = Ext.mk₀ f - Ext.mk₀ g := by
  simp [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg]

/-- An abstract dyadic contraction on `X`: an action of `P ℤ` on `X` whose zeroth finite slice is
`𝟙 X`, and which is invariant under the dyadic split map. -/
class DyadicContractible (X : LightCondAb) : Type 2 where
  action : P ℤ ⊗ X ⟶ X
  firstSlice : pBasisTensorSlice X 0 ≫ action = 𝟙 X
  split_action : (pSplitMap ▷ X) ≫ action = action

private lemma ext_eq_zero_of_dyadicContractionData_of_precomp_bijective
    (X : LightCondAb) (E : Solid) (n : ℕ)
    (action : P ℤ ⊗ X ⟶ X)
    (firstSlice : pBasisTensorSlice X 0 ≫ action = 𝟙 X)
    (split_action : (pSplitMap ▷ X) ≫ action = action)
    (hσ : Function.Bijective
      (fun α : Ext (P ℤ ⊗ X) ((isSolid.ι).obj E) n =>
        (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp α (zero_add n)))
    (α : Ext X ((isSolid.ι).obj E) n) :
    α = 0 := by
  let Y := (isSolid.ι).obj E
  let σ : P ℤ ⊗ X ⟶ P ℤ ⊗ X := (oneMinusShift ℤ) ▷ X
  let F' : P ℤ ⊗ X ⟶ P ℤ ⊗ X := pSplitMap ▷ X
  let G' : P ℤ ⊗ X ⟶ P ℤ ⊗ X := pOddMap ▷ X
  let ι0 : X ⟶ P ℤ ⊗ X := pBasisTensorSlice X 0
  let ι1 : X ⟶ P ℤ ⊗ X := pBasisTensorSlice X 1
  rcases hσ.2 ((Ext.mk₀ action).comp α (zero_add n)) with ⟨β, hβ⟩
  change (Ext.mk₀ σ).comp β (zero_add n) = (Ext.mk₀ action).comp α (zero_add n)
    at hβ
  have hFG : F' ≫ σ = σ ≫ G' := by
    dsimp [F', σ, G']
    exact pSplitMap_tensor_comp_oneMinusShift_tensor X
  have hσG :
      (Ext.mk₀ σ).comp ((Ext.mk₀ G').comp β (zero_add n)) (zero_add n) =
        (Ext.mk₀ σ).comp β (zero_add n) := by
    calc
      (Ext.mk₀ σ).comp ((Ext.mk₀ G').comp β (zero_add n)) (zero_add n)
          = (Ext.mk₀ (σ ≫ G')).comp β (zero_add n) := by
            rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ (F' ≫ σ)).comp β (zero_add n) := by rw [← hFG]
      _ = (Ext.mk₀ F').comp ((Ext.mk₀ σ).comp β (zero_add n)) (zero_add n) := by
            rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ F').comp ((Ext.mk₀ action).comp α (zero_add n)) (zero_add n) := by
            rw [hβ]
      _ = (Ext.mk₀ (F' ≫ action)).comp α (zero_add n) := by
            rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ action).comp α (zero_add n) := by
            rw [split_action]
      _ = (Ext.mk₀ σ).comp β (zero_add n) := by rw [← hβ]
  have hGβ : (Ext.mk₀ G').comp β (zero_add n) = β := hσ.1 hσG
  let β0 : Ext X Y n := (Ext.mk₀ ι0).comp β (zero_add n)
  let β1 : Ext X Y n := (Ext.mk₀ ι1).comp β (zero_add n)
  have hdiff : β0 - β1 = α := by
    calc
      β0 - β1 = (Ext.mk₀ (ι0 - ι1)).comp β (zero_add n) := by
        dsimp [β0, β1]
        rw [ext_mk₀_sub]
        simp [sub_eq_add_neg]
      _ = (Ext.mk₀ (ι0 ≫ σ)).comp β (zero_add n) := by
        rw [pBasisTensorSlice_comp_oneMinusShift]
      _ = (Ext.mk₀ ι0).comp ((Ext.mk₀ σ).comp β (zero_add n)) (zero_add n) := by
        rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ ι0).comp ((Ext.mk₀ action).comp α (zero_add n)) (zero_add n) := by
        rw [hβ]
      _ = (Ext.mk₀ (ι0 ≫ action)).comp α (zero_add n) := by
        rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ (𝟙 X)).comp α (zero_add n) := by
        rw [firstSlice]
      _ = α := by simp
  have hβ10 : β1 = β0 := by
    calc
      β1 = (Ext.mk₀ (ι0 ≫ G')).comp β (zero_add n) := by
        dsimp [β1, ι0, ι1, G']
        rw [pBasisTensorSlice_comp_pOddMap]
      _ = (Ext.mk₀ ι0).comp ((Ext.mk₀ G').comp β (zero_add n)) (zero_add n) := by
        rw [Ext.mk₀_comp_mk₀_assoc]
      _ = (Ext.mk₀ ι0).comp β (zero_add n) := by rw [hGβ]
      _ = β0 := rfl
  calc
    α = β0 - β1 := hdiff.symm
    _ = 0 := by rw [hβ10]; simp

/-- Degree-zero Ext vanishing for dyadically contractible objects against solid targets. -/
lemma ext0_eq_zero_of_dyadicContractible
    (X : LightCondAb) [DyadicContractible X]
    (E : Solid) (α : Ext X ((isSolid.ι).obj E) 0) :
    α = 0 :=
  ext_eq_zero_of_dyadicContractionData_of_precomp_bijective X E 0
    (DyadicContractible.action (X := X))
    (DyadicContractible.firstSlice (X := X))
    (DyadicContractible.split_action (X := X))
    (ext0_precomp_oneMinusShift_tensor_bijective X E) α

/-- Ordinary Hom vanishing for dyadically contractible objects against solid targets. -/
lemma hom_eq_zero_of_dyadicContractible
    (X : LightCondAb) [DyadicContractible X]
    (E : Solid) (f : X ⟶ (isSolid.ι).obj E) :
    f = 0 := by
  have h : Ext.mk₀ f = 0 := ext0_eq_zero_of_dyadicContractible X E (Ext.mk₀ f)
  exact (Ext.mk₀_eq_zero_iff f).1 h

/-- Ext¹ vanishing for dyadically contractible objects against solid targets. -/
lemma ext1_eq_zero_of_dyadicContractible
    (X : LightCondAb) [DyadicContractible X]
    (E : Solid) (α : Ext X ((isSolid.ι).obj E) 1) :
    α = 0 :=
  ext_eq_zero_of_dyadicContractionData_of_precomp_bijective X E 1
    (DyadicContractible.action (X := X))
    (DyadicContractible.firstSlice (X := X))
    (DyadicContractible.split_action (X := X))
    (ext1_precomp_oneMinusShift_tensor_bijective X E) α

/-- The dyadic coefficient as a continuous function on `ℕ∪∞`, with value `0` at `∞`. -/
def dyadicCoeffNinf : C((ℕ∪{∞} : LightProfinite), ℝ) where
  toFun x :=
    match x with
    | ∞ => 0
    | OnePoint.some n => dyadicCoeff n
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    simpa using tendsto_dyadicCoeff_atTop_zero

@[simp]
lemma dyadicCoeffNinf_finite (n : ℕ) :
    dyadicCoeffNinf (n : ℕ∪{∞}) = dyadicCoeff n := rfl

@[simp]
lemma dyadicCoeffNinf_infty : dyadicCoeffNinf (∞ : ℕ∪{∞}) = 0 := rfl

lemma dyadicCoeff_nonneg (n : ℕ) : 0 ≤ dyadicCoeff n := by
  unfold dyadicCoeff
  positivity

lemma dyadicCoeff_le_one (n : ℕ) : dyadicCoeff n ≤ 1 := by
  unfold dyadicCoeff
  exact pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 1)

lemma dyadicCoeffNinf_abs_le_one (a : ℕ∪{∞}) : ‖dyadicCoeffNinf a‖ ≤ (1 : ℝ) := by
  cases a using OnePoint.rec with
  | infty =>
      change ‖(0 : ℝ)‖ ≤ (1 : ℝ)
      norm_num
  | coe n =>
      change |dyadicCoeff n| ≤ (1 : ℝ)
      rw [abs_of_nonneg (dyadicCoeff_nonneg n)]
      exact dyadicCoeff_le_one n

lemma dyadicCoeffNinf_odd_add_even (a : ℕ∪{∞}) :
    dyadicCoeffNinf (LightProfinite.oddMap a) +
        dyadicCoeffNinf (LightProfinite.evenMap a) = dyadicCoeffNinf a := by
  cases a using OnePoint.rec with
  | infty =>
      change (0 : ℝ) + 0 = 0
      norm_num
  | coe n =>
      change dyadicCoeff (2 * n + 1) + dyadicCoeff (2 * n + 2) = dyadicCoeff n
      exact dyadicCoeff_pair_sum n

/-- Pull the continuous dyadic coefficient back along a map to `ℕ∪∞`. -/
def dyadicScalarFunction {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) : C(S, ℝ) :=
  dyadicCoeffNinf.comp f.hom.hom

lemma dyadicScalarFunction_odd_add_even {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (s : S) :
    dyadicScalarFunction (f ≫ LightProfinite.oddMap) s +
        dyadicScalarFunction (f ≫ LightProfinite.evenMap) s =
      dyadicScalarFunction f s := by
  exact dyadicCoeffNinf_odd_add_even (f s)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
lemma freeTensorHomPresheafComposite_precomp_left_map
    (X Y : LightProfinite) (φ : X ⟶ Y)
    (B C : LightCondAb) (g : ((free ℤ).obj Y.toCondensed) ⊗ B ⟶ C) :
    freeTensorHomPresheafComposite X B C
        ((((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ▷ B) ≫ g) =
      ((Functor.whiskerRight (lightProfiniteToLightCondSet.map φ).hom (ModuleCat.free ℤ)) ▷
          B.obj) ≫ freeTensorHomPresheafComposite Y B C g := by
  let L := presheafToSheaf (coherentTopology LightProfinite) (ModuleCat ℤ)
  let FX : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := X.toCondensed.obj ⋙ ModuleCat.free ℤ
  let FY : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := Y.toCondensed.obj ⋙ ModuleCat.free ℤ
  let G : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ := B.obj
  let η : FX ⟶ FY := Functor.whiskerRight (lightProfiniteToLightCondSet.map φ).hom
    (ModuleCat.free ℤ)
  let cB : L.obj G ⟶ B :=
    (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).counit.app B
  let g' : L.obj FY ⊗ B ⟶ C := g
  dsimp [freeTensorHomPresheafComposite]
  change toSheafify (coherentTopology LightProfinite) (FX ⊗ G) ≫
      (((Functor.Monoidal.μIso L FX G).inv ≫ (L.obj FX ◁ cB) ≫
        ((L.map η ▷ B) ≫ g')).hom) =
    (η ▷ G) ≫
      (toSheafify (coherentTopology LightProfinite) (FY ⊗ G) ≫
        (((Functor.Monoidal.μIso L FY G).inv ≫ (L.obj FY ◁ cB) ≫ g').hom))
  slice_rhs 1 3 => rw [CategoryTheory.toSheafify_naturality]
  simp only [Category.assoc]
  have hμinv : L.map (η ▷ G) ≫ (Functor.Monoidal.μIso L FY G).inv =
      (Functor.Monoidal.μIso L FX G).inv ≫ (L.map η ▷ L.obj G) := by
    apply (cancel_mono (Functor.Monoidal.μIso L FY G).hom).1
    calc
      (L.map (η ▷ G) ≫ (Functor.Monoidal.μIso L FY G).inv) ≫
          (Functor.Monoidal.μIso L FY G).hom
          = L.map (η ▷ G) := by simp [Category.assoc]
      _ = (Functor.Monoidal.μIso L FX G).inv ≫
            ((Functor.Monoidal.μIso L FX G).hom ≫ L.map (η ▷ G)) := by simp
      _ = (Functor.Monoidal.μIso L FX G).inv ≫
            ((L.map η ▷ L.obj G) ≫ (Functor.Monoidal.μIso L FY G).hom) := by
              have hμ := Functor.LaxMonoidal.μ_natural_left L η G
              change (L.map η ▷ L.obj G) ≫ (Functor.Monoidal.μIso L FY G).hom =
                (Functor.Monoidal.μIso L FX G).hom ≫ L.map (η ▷ G) at hμ
              rw [← hμ]
      _ = ((Functor.Monoidal.μIso L FX G).inv ≫ (L.map η ▷ L.obj G)) ≫
            (Functor.Monoidal.μIso L FY G).hom := by simp [Category.assoc]
  have hwhisker : (L.map η ▷ L.obj G) ≫ (L.obj FY ◁ cB) =
      (L.obj FX ◁ cB) ≫ (L.map η ▷ B) := by
    rw [whisker_exchange]
  have hsheaf : L.map (η ▷ G) ≫ (Functor.Monoidal.μIso L FY G).inv ≫
        (L.obj FY ◁ cB) ≫ g' =
      (Functor.Monoidal.μIso L FX G).inv ≫ (L.obj FX ◁ cB) ≫
        ((L.map η ▷ B) ≫ g') := by
    calc
      L.map (η ▷ G) ≫ (Functor.Monoidal.μIso L FY G).inv ≫
          (L.obj FY ◁ cB) ≫ g'
          = ((Functor.Monoidal.μIso L FX G).inv ≫ (L.map η ▷ L.obj G)) ≫
              (L.obj FY ◁ cB) ≫ g' := by rw [← Category.assoc, hμinv]
      _ = (Functor.Monoidal.μIso L FX G).inv ≫
              ((L.map η ▷ L.obj G) ≫ (L.obj FY ◁ cB)) ≫ g' := by
            simp [Category.assoc]
      _ = (Functor.Monoidal.μIso L FX G).inv ≫
              ((L.obj FX ◁ cB) ≫ (L.map η ▷ B)) ≫ g' := by rw [hwhisker]
      _ = (Functor.Monoidal.μIso L FX G).inv ≫ (L.obj FX ◁ cB) ≫
              ((L.map η ▷ B) ≫ g') := by simp [Category.assoc]
  have hinside :
      CategoryTheory.sheafifyMap (coherentTopology LightProfinite) (η ▷ G) ≫
        (((Functor.Monoidal.μIso L FY G).inv ≫ (L.obj FY ◁ cB) ≫ g').hom) =
      (((Functor.Monoidal.μIso L FX G).inv ≫ (L.obj FX ◁ cB) ≫
        ((L.map η ▷ B) ≫ g')).hom) := by
    change (L.map (η ▷ G) ≫ (Functor.Monoidal.μIso L FY G).inv ≫
        (L.obj FY ◁ cB) ≫ g').hom =
      ((Functor.Monoidal.μIso L FX G).inv ≫ (L.obj FX ◁ cB) ≫
        ((L.map η ▷ B) ≫ g')).hom
    exact congrArg (fun q => q.hom) hsheaf
  rw [hinside]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
lemma freeTensorHomEval_map_left (X Y : LightProfinite) (φ : X ⟶ Y)
    (B C : LightCondAb) (g : ((free ℤ).obj Y.toCondensed) ⊗ B ⟶ C)
    (S : LightProfinite) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B C
        ((((free ℤ).map (lightProfiniteToLightCondSet.map φ)) ▷ B) ≫ g) S f r m =
      freeTensorHomEval Y B C g S (f ≫ φ) r m := by
  dsimp [freeTensorHomEval]
  rw [freeTensorHomPresheafComposite_precomp_left_map]
  change (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      (((Functor.whiskerRight (lightProfiniteToLightCondSet.map φ).hom (ModuleCat.free ℤ) ▷
        B.obj).app ⟨S⟩) ((Finsupp.single f r) ⊗ₜ[ℤ] m)) =
    (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      ((Finsupp.single (f ≫ φ) r) ⊗ₜ[ℤ] m)
  change (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      ((((Functor.whiskerRight (lightProfiniteToLightCondSet.map φ).hom (ModuleCat.free ℤ)).app
        ⟨S⟩) ⊗ₘ (𝟙 (B.obj.obj ⟨S⟩))) ((Finsupp.single f r) ⊗ₜ[ℤ] m)) =
    (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      ((Finsupp.single (f ≫ φ) r) ⊗ₜ[ℤ] m)
  change (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      ((TensorProduct.map (Finsupp.lmapDomain ℤ ℤ
        ((lightProfiniteToLightCondSet.map φ).hom.app ⟨S⟩))
        (LinearMap.id : B.obj.obj ⟨S⟩ →ₗ[ℤ] B.obj.obj ⟨S⟩))
          ((Finsupp.single f r) ⊗ₜ[ℤ] m)) =
    (freeTensorHomPresheafComposite Y B C g).app ⟨S⟩
      ((Finsupp.single (f ≫ φ) r) ⊗ₜ[ℤ] m)
  rw [TensorProduct.map_tmul]
  congr 1
  rw [Finsupp.lmapDomain_apply]
  rw [Finsupp.mapDomain_single]
  rfl

lemma freeTensorHomEval_add (X : LightProfinite) (B C : LightCondAb)
    (g₁ g₂ : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C)
    (S : LightProfinite) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B C (g₁ + g₂) S f r m =
      freeTensorHomEval X B C g₁ S f r m + freeTensorHomEval X B C g₂ S f r m := by
  rfl

/-- Tensor finite slices are natural in the right tensor factor. -/
lemma pBasisTensorSlice_naturality {X Y : LightCondAb} (f : X ⟶ Y) (n : ℕ) :
    pBasisTensorSlice X n ≫ (P ℤ ◁ f) = f ≫ pBasisTensorSlice Y n := by
  dsimp [pBasisTensorSlice]
  rw [leftUnitor_inv_naturality_assoc]
  slice_lhs 2 3 => rw [← whisker_exchange]

/-- Multiplication by a real scalar on the real-line condensed abelian group. -/
noncomputable def realCondensedAbScalarEndo (c : ℝ) : realCondensedAb ⟶ realCondensedAb where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => (ContinuousMap.const S.unop c) * (show C(S.unop, ℝ) from x)
      map_add' := by
        intro x y
        change (ContinuousMap.const S.unop c) *
            ((show C(S.unop, ℝ) from x) + (show C(S.unop, ℝ) from y)) =
          (ContinuousMap.const S.unop c) * (show C(S.unop, ℝ) from x) +
            (ContinuousMap.const S.unop c) * (show C(S.unop, ℝ) from y)
        ext s
        simp [mul_add]
      map_smul' := by
        intro a x
        change (ContinuousMap.const S.unop c) * (a • (show C(S.unop, ℝ) from x)) =
          a • ((ContinuousMap.const S.unop c) * (show C(S.unop, ℝ) from x))
        ext s
        simp [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] }
    naturality := by
      intro S T φ
      ext x
      rfl }

@[simp]
lemma realCondensedAbScalarEndo_one : realCondensedAbScalarEndo 1 = 𝟙 realCondensedAb := by
  ext S x
  change (ContinuousMap.const S.unop 1) * (show C(S.unop, ℝ) from x) =
    (show C(S.unop, ℝ) from x)
  ext s
  change (1 : ℝ) * ((show C(S.unop, ℝ) from x) s) = _
  exact one_mul _

lemma realCondensedAbScalarEndo_add (c d : ℝ) :
    realCondensedAbScalarEndo (c + d) = realCondensedAbScalarEndo c +
      realCondensedAbScalarEndo d := by
  ext S x
  change (ContinuousMap.const S.unop (c + d)) * (show C(S.unop, ℝ) from x) =
    (ContinuousMap.const S.unop c) * (show C(S.unop, ℝ) from x) +
      (ContinuousMap.const S.unop d) * (show C(S.unop, ℝ) from x)
  ext s
  change (c + d) * ((show C(S.unop, ℝ) from x) s) =
    c * ((show C(S.unop, ℝ) from x) s) + d * ((show C(S.unop, ℝ) from x) s)
  ring

noncomputable def realDyadicFamilyLinear (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) :
    realCondensedAb.obj.obj ⟨S⟩ →ₗ[ℤ] realCondensedAb.obj.obj ⟨S⟩ where
  toFun x := dyadicScalarFunction f * (show C(S, ℝ) from x)
  map_add' := by
    intro x y
    change dyadicScalarFunction f *
        ((show C(S, ℝ) from x) + (show C(S, ℝ) from y)) =
      dyadicScalarFunction f * (show C(S, ℝ) from x) +
        dyadicScalarFunction f * (show C(S, ℝ) from y)
    exact mul_add _ _ _
  map_smul' := by
    intro a x
    change dyadicScalarFunction f * (a • (show C(S, ℝ) from x)) =
      a • (dyadicScalarFunction f * (show C(S, ℝ) from x))
    ext s
    change dyadicScalarFunction f s * (a • (show C(S, ℝ) from x) s) =
      a • (dyadicScalarFunction f s * (show C(S, ℝ) from x) s)
    simp [zsmul_eq_mul]
    ring

lemma realDyadicFamilyLinear_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : realCondensedAb.obj.obj ⟨S⟩) :
    realCondensedAb.obj.map g.op (realDyadicFamilyLinear S f m) =
      realDyadicFamilyLinear T (g ≫ f) (realCondensedAb.obj.map g.op m) := by
  change (dyadicScalarFunction f * (show C(S, ℝ) from m)).comp g.hom.hom =
    dyadicScalarFunction (g ≫ f) * ((show C(S, ℝ) from m).comp g.hom.hom)
  ext t
  rfl

lemma realDyadicFamilyLinear_split (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (m : realCondensedAb.obj.obj ⟨S⟩) :
    realDyadicFamilyLinear S (f ≫ LightProfinite.oddMap) m +
        realDyadicFamilyLinear S (f ≫ LightProfinite.evenMap) m =
      realDyadicFamilyLinear S f m := by
  change dyadicScalarFunction (f ≫ LightProfinite.oddMap) * (show C(S, ℝ) from m) +
      dyadicScalarFunction (f ≫ LightProfinite.evenMap) * (show C(S, ℝ) from m) =
    dyadicScalarFunction f * (show C(S, ℝ) from m)
  ext s
  change dyadicScalarFunction (f ≫ LightProfinite.oddMap) s * (show C(S, ℝ) from m) s +
      dyadicScalarFunction (f ≫ LightProfinite.evenMap) s * (show C(S, ℝ) from m) s =
    dyadicScalarFunction f s * (show C(S, ℝ) from m) s
  rw [← add_mul]
  rw [dyadicScalarFunction_odd_add_even]

lemma realDyadicFamilyMap_natPoint (n : ℕ) :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) realCondensedAb realCondensedAb
      realDyadicFamilyLinear realDyadicFamilyLinear_naturality (natPoint n) =
    realCondensedAbScalarEndo (dyadicCoeff n) := by
  ext S x
  change realDyadicFamilyLinear S.unop (toPointMap S.unop ≫ natPoint n) x =
    (realCondensedAbScalarEndo (dyadicCoeff n)).hom.app S x
  change dyadicScalarFunction (toPointMap S.unop ≫ natPoint n) *
      (show C(S.unop, ℝ) from x) =
    (ContinuousMap.const S.unop (dyadicCoeff n)) * (show C(S.unop, ℝ) from x)
  ext s
  rfl

lemma realDyadicFamilyMap_infty :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) realCondensedAb realCondensedAb
      realDyadicFamilyLinear realDyadicFamilyLinear_naturality ι = 0 := by
  ext S x
  change realDyadicFamilyLinear S.unop (toPointMap S.unop ≫ ι) x =
    (0 : realCondensedAb ⟶ realCondensedAb).hom.app S x
  change dyadicScalarFunction (toPointMap S.unop ≫ ι) * (show C(S.unop, ℝ) from x) = 0
  ext s
  change (0 : ℝ) * (show C(S.unop, ℝ) from x) s = 0
  simp

noncomputable def realDyadicNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ realCondensedAb ⟶ realCondensedAb :=
  freeTensorDescLin (ℕ∪{∞} : LightProfinite) realCondensedAb realCondensedAb
    realDyadicFamilyLinear realDyadicFamilyLinear_naturality

lemma realDyadicNumerator_slice (n : ℕ) :
    numeratorSlice realCondensedAb realCondensedAb n realDyadicNumerator =
      realCondensedAbScalarEndo (dyadicCoeff n) := by
  dsimp [numeratorSlice, freeNatBasis, realDyadicNumerator]
  rw [freeTensorDescLin_point]
  exact realDyadicFamilyMap_natPoint n

lemma realDyadicNumerator_infty :
    inftySlice realCondensedAb realCondensedAb realDyadicNumerator = 0 := by
  dsimp [inftySlice, freeInftyBasis, P_map, realDyadicNumerator]
  rw [freeTensorDescLin_point]
  exact realDyadicFamilyMap_infty

lemma realDyadicNumerator_kills :
    (P_map ℤ ▷ realCondensedAb) ≫ realDyadicNumerator = 0 :=
  numerator_kills_of_inftySlice_zero realCondensedAb realCondensedAb realDyadicNumerator
    realDyadicNumerator_infty

lemma realDyadicNumerator_comp_freeSplit :
    ((freeOddMap + freeEvenMap) ▷ realCondensedAb) ≫ realDyadicNumerator =
      realDyadicNumerator := by
  apply freeTensorHom_ext
  intro S f r m
  rw [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]
  rw [freeTensorHomEval_add]
  dsimp [freeOddMap, freeEvenMap, realDyadicNumerator]
  rw [freeTensorHomEval_map_left, freeTensorHomEval_map_left]
  rw [freeTensorHomEval_desc, freeTensorHomEval_desc, freeTensorHomEval_desc]
  rw [← zsmul_add]
  rw [realDyadicFamilyLinear_split]

/-- The dyadic action on `realCondensedAb`. -/
noncomputable def realDyadicAction : P ℤ ⊗ realCondensedAb ⟶ realCondensedAb :=
  pTensorDesc realCondensedAb realCondensedAb realDyadicNumerator realDyadicNumerator_kills

lemma realDyadicAction_slice (n : ℕ) :
    pBasisTensorSlice realCondensedAb n ≫ realDyadicAction =
      realCondensedAbScalarEndo (dyadicCoeff n) := by
  dsimp [realDyadicAction, pBasisTensorSlice]
  rw [pTensorDesc_slice]
  exact realDyadicNumerator_slice n

lemma realDyadicAction_split :
    (pSplitMap ▷ realCondensedAb) ≫ realDyadicAction = realDyadicAction := by
  haveI : Epi (P_proj ℤ ▷ realCondensedAb) := epi_P_proj_tensor realCondensedAb
  apply (cancel_epi (P_proj ℤ ▷ realCondensedAb)).1
  calc
    (P_proj ℤ ▷ realCondensedAb) ≫ ((pSplitMap ▷ realCondensedAb) ≫ realDyadicAction)
        = ((P_proj ℤ ≫ pSplitMap) ▷ realCondensedAb) ≫ realDyadicAction := by
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = (((freeOddMap + freeEvenMap) ≫ P_proj ℤ) ▷ realCondensedAb) ≫ realDyadicAction := by
          rw [P_proj_comp_pSplitMap]
    _ = ((freeOddMap + freeEvenMap) ▷ realCondensedAb) ≫
          (P_proj ℤ ▷ realCondensedAb) ≫ realDyadicAction := by
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = ((freeOddMap + freeEvenMap) ▷ realCondensedAb) ≫ realDyadicNumerator := by
          dsimp [realDyadicAction]
          rw [pTensorDesc_comp_proj]
    _ = realDyadicNumerator := realDyadicNumerator_comp_freeSplit
    _ = (P_proj ℤ ▷ realCondensedAb) ≫ realDyadicAction := by
          rw [realDyadicAction, pTensorDesc_comp_proj]

instance realCondensedAb_dyadicContractible : DyadicContractible realCondensedAb where
  action := realDyadicAction
  firstSlice := by
    rw [realDyadicAction_slice, dyadicCoeff_zero, realCondensedAbScalarEndo_one]
  split_action := realDyadicAction_split

/-- Coordinatewise scalar multiplication on the product of real sequences. -/
noncomputable def productRealSequencesScalarEndo (c : ℝ) :
    productRealSequences ⟶ productRealSequences := by
  dsimp [productRealSequences]
  exact Pi.lift fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
    realCondensedAbScalarEndo c

@[reassoc]
lemma productRealSequencesScalarEndo_π (c : ℝ) (j : ℕ) :
    productRealSequencesScalarEndo c ≫ Pi.π (fun _ : ℕ => realCondensedAb) j =
      Pi.π (fun _ : ℕ => realCondensedAb) j ≫ realCondensedAbScalarEndo c := by
  change (Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo c)) ≫ Pi.π (fun _ : ℕ => realCondensedAb) j =
    Pi.π (fun _ : ℕ => realCondensedAb) j ≫ realCondensedAbScalarEndo c
  rw [Pi.lift_π]

@[simp]
lemma productRealSequencesScalarEndo_one :
    productRealSequencesScalarEndo 1 = 𝟙 productRealSequences := by
  change (Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo 1)) = 𝟙 (∏ᶜ fun _ : ℕ => realCondensedAb)
  apply Pi.hom_ext
  intro j
  rw [Pi.lift_π, realCondensedAbScalarEndo_one]
  simp

lemma productRealSequencesScalarEndo_add (c d : ℝ) :
    productRealSequencesScalarEndo (c + d) = productRealSequencesScalarEndo c +
      productRealSequencesScalarEndo d := by
  change (Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo (c + d))) =
    (Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo c)) +
    (Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo d))
  apply Pi.hom_ext
  intro j
  rw [Pi.lift_π, Preadditive.add_comp, Pi.lift_π, Pi.lift_π,
    realCondensedAbScalarEndo_add]
  simp [Preadditive.comp_add]

/-- The product-real dyadic action, defined coordinatewise from the real-line action. -/
noncomputable def productRealDyadicAction :
    P ℤ ⊗ productRealSequences ⟶ productRealSequences := by
  dsimp [productRealSequences]
  exact Pi.lift fun j : ℕ => (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫ realDyadicAction

@[reassoc]
lemma productRealDyadicAction_π (j : ℕ) :
    productRealDyadicAction ≫ Pi.π (fun _ : ℕ => realCondensedAb) j =
      (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫ realDyadicAction := by
  change (Pi.lift (fun j : ℕ => (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫
      realDyadicAction)) ≫ Pi.π (fun _ : ℕ => realCondensedAb) j =
    (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫ realDyadicAction
  rw [Pi.lift_π]

lemma productRealDyadicAction_slice (n : ℕ) :
    pBasisTensorSlice productRealSequences n ≫ productRealDyadicAction =
      productRealSequencesScalarEndo (dyadicCoeff n) := by
  change pBasisTensorSlice (∏ᶜ fun _ : ℕ => realCondensedAb) n ≫
      (Pi.lift (fun j : ℕ => (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫
        realDyadicAction)) =
    Pi.lift (fun j : ℕ => Pi.π (fun _ : ℕ => realCondensedAb) j ≫
      realCondensedAbScalarEndo (dyadicCoeff n))
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.lift_π, Pi.lift_π]
  rw [← Category.assoc, pBasisTensorSlice_naturality]
  rw [Category.assoc, realDyadicAction_slice]

lemma productRealDyadicAction_split :
    (pSplitMap ▷ productRealSequences) ≫ productRealDyadicAction = productRealDyadicAction := by
  change (pSplitMap ▷ (∏ᶜ fun _ : ℕ => realCondensedAb)) ≫
      (Pi.lift (fun j : ℕ => (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫
        realDyadicAction)) =
    Pi.lift (fun j : ℕ => (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫
      realDyadicAction)
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.lift_π]
  calc
    (pSplitMap ▷ (∏ᶜ fun _ : ℕ => realCondensedAb)) ≫
        ((P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫ realDyadicAction)
        = ((P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫
            (pSplitMap ▷ realCondensedAb)) ≫ realDyadicAction := by
          rw [← Category.assoc]
          rw [whisker_exchange]
    _ = (P ℤ ◁ Pi.π (fun _ : ℕ => realCondensedAb) j) ≫ realDyadicAction := by
          rw [Category.assoc, realDyadicAction_split]

instance productRealSequences_dyadicContractible : DyadicContractible productRealSequences where
  action := productRealDyadicAction
  firstSlice := by
    rw [productRealDyadicAction_slice, dyadicCoeff_zero, productRealSequencesScalarEndo_one]
  split_action := productRealDyadicAction_split

noncomputable def boundedRealScalarSection {S : LightProfinite} (c : ℝ)
    (x : BoundedRealSeqSection S) : BoundedRealSeqSection S where
  val n := ContinuousMap.const S c * x.val n
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    obtain ⟨K, hK⟩ := exists_nat_ge (‖c‖ * (N : ℝ))
    refine ⟨K, ?_⟩
    intro s n
    calc
      ‖(ContinuousMap.const S c * x.val n) s‖ = ‖c‖ * ‖x.val n s‖ := by simp [norm_mul]
      _ ≤ ‖c‖ * (N : ℝ) := mul_le_mul_of_nonneg_left (hN s n) (norm_nonneg c)
      _ ≤ (K : ℝ) := hK

/-- Scalar multiplication on bounded real sequences. -/
noncomputable def boundedRealSequencesScalarEndo (c : ℝ) :
    boundedRealSequences ⟶ boundedRealSequences where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => boundedRealScalarSection c (show BoundedRealSeqSection S.unop from x)
      map_add' := by
        intro x y
        apply BoundedRealSeqSection.ext_apply
        intro n s
        simp [boundedRealScalarSection, mul_add]
      map_smul' := by
        intro a x
        apply BoundedRealSeqSection.ext_apply
        intro n s
        simp [boundedRealScalarSection]
        ring }
    naturality := by
      intro S T φ
      ext x
      rfl }

@[simp]
lemma boundedRealSequencesScalarEndo_one :
    boundedRealSequencesScalarEndo 1 = 𝟙 boundedRealSequences := by
  ext S x
  apply BoundedRealSeqSection.ext_apply
  intro n s
  change (1 : ℝ) * (show BoundedRealSeqSection S.unop from x).val n s =
    (show BoundedRealSeqSection S.unop from x).val n s
  simp

lemma boundedRealSequencesScalarEndo_add (c d : ℝ) :
    boundedRealSequencesScalarEndo (c + d) = boundedRealSequencesScalarEndo c +
      boundedRealSequencesScalarEndo d := by
  ext S x
  apply BoundedRealSeqSection.ext_apply
  intro n s
  change (c + d) * (show BoundedRealSeqSection S.unop from x).val n s =
    c * (show BoundedRealSeqSection S.unop from x).val n s +
      d * (show BoundedRealSeqSection S.unop from x).val n s
  ring

noncomputable def boundedRealDyadicSection {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (x : BoundedRealSeqSection S) : BoundedRealSeqSection S where
  val n := dyadicScalarFunction f * x.val n
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    refine ⟨N, ?_⟩
    intro s n
    calc
      ‖(dyadicScalarFunction f * x.val n) s‖ =
          ‖dyadicScalarFunction f s‖ * ‖x.val n s‖ := by simp [norm_mul]
      _ ≤ 1 * (N : ℝ) := by
          exact mul_le_mul (dyadicCoeffNinf_abs_le_one (f s)) (hN s n) (norm_nonneg _)
            (by norm_num)
      _ = (N : ℝ) := one_mul _

noncomputable def boundedRealDyadicFamilyLinear (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) :
    boundedRealSequences.obj.obj ⟨S⟩ →ₗ[ℤ] boundedRealSequences.obj.obj ⟨S⟩ where
  toFun x := boundedRealDyadicSection f (show BoundedRealSeqSection S from x)
  map_add' := by
    intro x y
    apply BoundedRealSeqSection.ext_apply
    intro n s
    change (dyadicScalarFunction f s) * (((show BoundedRealSeqSection S from x).val n s) +
        ((show BoundedRealSeqSection S from y).val n s)) =
      (dyadicScalarFunction f s) * (show BoundedRealSeqSection S from x).val n s +
        (dyadicScalarFunction f s) * (show BoundedRealSeqSection S from y).val n s
    ring
  map_smul' := by
    intro a x
    apply BoundedRealSeqSection.ext_apply
    intro n s
    change (dyadicScalarFunction f s) * ((a • (show BoundedRealSeqSection S from x)).val n s) =
      (a • boundedRealDyadicSection f (show BoundedRealSeqSection S from x)).val n s
    rw [BoundedRealSeqSection.val_zsmul]
    change (dyadicScalarFunction f s) * ((a • (show BoundedRealSeqSection S from x).val n) s) =
      (a • (dyadicScalarFunction f * (show BoundedRealSeqSection S from x).val n)) s
    simp [zsmul_eq_mul]
    ring

lemma boundedRealDyadicFamilyLinear_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : boundedRealSequences.obj.obj ⟨S⟩) :
    boundedRealSequences.obj.map g.op (boundedRealDyadicFamilyLinear S f m) =
      boundedRealDyadicFamilyLinear T (g ≫ f) (boundedRealSequences.obj.map g.op m) := by
  apply BoundedRealSeqSection.ext_apply
  intro n t
  rfl

lemma boundedRealDyadicFamilyLinear_split (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : boundedRealSequences.obj.obj ⟨S⟩) :
    boundedRealDyadicFamilyLinear S (f ≫ LightProfinite.oddMap) m +
        boundedRealDyadicFamilyLinear S (f ≫ LightProfinite.evenMap) m =
      boundedRealDyadicFamilyLinear S f m := by
  apply BoundedRealSeqSection.ext_apply
  intro n s
  change (dyadicScalarFunction (f ≫ LightProfinite.oddMap) s) *
        (show BoundedRealSeqSection S from m).val n s +
      (dyadicScalarFunction (f ≫ LightProfinite.evenMap) s) *
        (show BoundedRealSeqSection S from m).val n s =
    (dyadicScalarFunction f s) * (show BoundedRealSeqSection S from m).val n s
  rw [← add_mul]
  rw [dyadicScalarFunction_odd_add_even]

lemma boundedRealDyadicFamilyMap_natPoint (n : ℕ) :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedRealSequences boundedRealSequences
      boundedRealDyadicFamilyLinear boundedRealDyadicFamilyLinear_naturality (natPoint n) =
    boundedRealSequencesScalarEndo (dyadicCoeff n) := by
  ext S x
  apply BoundedRealSeqSection.ext_apply
  intro k s
  rfl

lemma boundedRealDyadicFamilyMap_infty :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedRealSequences boundedRealSequences
      boundedRealDyadicFamilyLinear boundedRealDyadicFamilyLinear_naturality ι = 0 := by
  ext S x
  apply BoundedRealSeqSection.ext_apply
  intro k s
  change (0 : ℝ) * (show BoundedRealSeqSection S.unop from x).val k s = 0
  simp

noncomputable def boundedRealDyadicNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ boundedRealSequences ⟶ boundedRealSequences :=
  freeTensorDescLin (ℕ∪{∞} : LightProfinite) boundedRealSequences boundedRealSequences
    boundedRealDyadicFamilyLinear boundedRealDyadicFamilyLinear_naturality

lemma boundedRealDyadicNumerator_slice (n : ℕ) :
    numeratorSlice boundedRealSequences boundedRealSequences n boundedRealDyadicNumerator =
      boundedRealSequencesScalarEndo (dyadicCoeff n) := by
  dsimp [numeratorSlice, freeNatBasis, boundedRealDyadicNumerator]
  rw [freeTensorDescLin_point]
  exact boundedRealDyadicFamilyMap_natPoint n

lemma boundedRealDyadicNumerator_infty :
    inftySlice boundedRealSequences boundedRealSequences boundedRealDyadicNumerator = 0 := by
  dsimp [inftySlice, freeInftyBasis, P_map, boundedRealDyadicNumerator]
  rw [freeTensorDescLin_point]
  exact boundedRealDyadicFamilyMap_infty

lemma boundedRealDyadicNumerator_kills :
    (P_map ℤ ▷ boundedRealSequences) ≫ boundedRealDyadicNumerator = 0 :=
  numerator_kills_of_inftySlice_zero boundedRealSequences boundedRealSequences
    boundedRealDyadicNumerator boundedRealDyadicNumerator_infty

lemma boundedRealDyadicNumerator_comp_freeSplit :
    ((freeOddMap + freeEvenMap) ▷ boundedRealSequences) ≫ boundedRealDyadicNumerator =
      boundedRealDyadicNumerator := by
  apply freeTensorHom_ext
  intro S f r m
  rw [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]
  rw [freeTensorHomEval_add]
  dsimp [freeOddMap, freeEvenMap, boundedRealDyadicNumerator]
  rw [freeTensorHomEval_map_left, freeTensorHomEval_map_left]
  rw [freeTensorHomEval_desc, freeTensorHomEval_desc, freeTensorHomEval_desc]
  rw [← zsmul_add]
  rw [boundedRealDyadicFamilyLinear_split]

/-- The dyadic action on bounded real sequences. -/
noncomputable def boundedRealDyadicAction :
    P ℤ ⊗ boundedRealSequences ⟶ boundedRealSequences :=
  pTensorDesc boundedRealSequences boundedRealSequences boundedRealDyadicNumerator
    boundedRealDyadicNumerator_kills

lemma boundedRealDyadicAction_slice (n : ℕ) :
    pBasisTensorSlice boundedRealSequences n ≫ boundedRealDyadicAction =
      boundedRealSequencesScalarEndo (dyadicCoeff n) := by
  dsimp [boundedRealDyadicAction, pBasisTensorSlice]
  rw [pTensorDesc_slice]
  exact boundedRealDyadicNumerator_slice n

lemma boundedRealDyadicAction_split :
    (pSplitMap ▷ boundedRealSequences) ≫ boundedRealDyadicAction = boundedRealDyadicAction := by
  haveI : Epi (P_proj ℤ ▷ boundedRealSequences) := epi_P_proj_tensor boundedRealSequences
  apply (cancel_epi (P_proj ℤ ▷ boundedRealSequences)).1
  calc
    (P_proj ℤ ▷ boundedRealSequences) ≫
        ((pSplitMap ▷ boundedRealSequences) ≫ boundedRealDyadicAction)
        = ((P_proj ℤ ≫ pSplitMap) ▷ boundedRealSequences) ≫ boundedRealDyadicAction := by
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = (((freeOddMap + freeEvenMap) ≫ P_proj ℤ) ▷ boundedRealSequences) ≫
          boundedRealDyadicAction := by
          rw [P_proj_comp_pSplitMap]
    _ = ((freeOddMap + freeEvenMap) ▷ boundedRealSequences) ≫
          (P_proj ℤ ▷ boundedRealSequences) ≫ boundedRealDyadicAction := by
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = ((freeOddMap + freeEvenMap) ▷ boundedRealSequences) ≫ boundedRealDyadicNumerator := by
          dsimp [boundedRealDyadicAction]
          rw [pTensorDesc_comp_proj]
    _ = boundedRealDyadicNumerator := boundedRealDyadicNumerator_comp_freeSplit
    _ = (P_proj ℤ ▷ boundedRealSequences) ≫ boundedRealDyadicAction := by
          rw [boundedRealDyadicAction, pTensorDesc_comp_proj]

instance boundedRealSequences_dyadicContractible : DyadicContractible boundedRealSequences where
  action := boundedRealDyadicAction
  firstSlice := by
    rw [boundedRealDyadicAction_slice, dyadicCoeff_zero, boundedRealSequencesScalarEndo_one]
  split_action := boundedRealDyadicAction_split

/-- Camargo Theorem 3.2.4(4), recorded as Hom-vanishing for real condensed abelian groups. -/
lemma hom_realCondensedAb_solid_eq_zero
    (E : Solid) (f : realCondensedAb ⟶ (isSolid.ι).obj E) : f = 0 :=
  hom_eq_zero_of_dyadicContractible realCondensedAb E f

/-- Lean's `IsZero` is not a typeclass, so this declaration cannot be registered as an
`instance`; keep the downstream-facing `inst...` name from the SPG12d sub-spec. -/
lemma instIsZero_solidification_realCondensedAb :
    IsZero (solidification.obj realCondensedAb) := by
  rw [IsZero.iff_id_eq_zero]
  let E : Solid := solidification.obj realCondensedAb
  have hzero : solidificationAdjunction.homEquiv realCondensedAb E (𝟙 E) = 0 :=
    hom_realCondensedAb_solid_eq_zero E
      (solidificationAdjunction.homEquiv realCondensedAb E (𝟙 E))
  apply (solidificationAdjunction.homEquiv realCondensedAb E).injective
  rw [hzero]
  rw [Adjunction.homAddEquiv_zero]

instance boundedRealToProductReal_mono : Mono boundedRealToProductReal := by
  apply Sheaf.mono_of_injective
  intro S x y hxy
  apply (boundedRealSequencesSectionsEquiv S.unop).injective
  apply Subtype.ext
  funext n
  have hcoord := congrArg (fun z => productRealSequencesSectionsEquiv S.unop z n) hxy
  change productRealSequencesSectionsEquiv S.unop
        ((boundedRealToProductReal.hom.app ⟨S.unop⟩) x) n =
      productRealSequencesSectionsEquiv S.unop
        ((boundedRealToProductReal.hom.app ⟨S.unop⟩) y) n at hcoord
  rw [boundedRealToProductReal_apply_coord, boundedRealToProductReal_apply_coord] at hcoord
  exact hcoord

instance boundedToProduct_mono : Mono boundedToProduct := by
  apply Sheaf.mono_of_injective
  intro S x y hxy
  apply (boundedIntSequencesSectionsEquiv S.unop).injective
  change (boundedIntSequencesSectionsEquiv S.unop x : BoundedIntSeqSection S.unop) =
    boundedIntSequencesSectionsEquiv S.unop y
  apply BoundedIntSeqSection.ext
  intro n
  have hcoord := congrArg (fun z => productIntLocallyConstantSectionsEquiv S.unop z n) hxy
  change productIntLocallyConstantSectionsEquiv S.unop
        ((boundedToProduct.hom.app ⟨S.unop⟩) x) n =
      productIntLocallyConstantSectionsEquiv S.unop
        ((boundedToProduct.hom.app ⟨S.unop⟩) y) n at hcoord
  rw [boundedToProduct_apply_coord, boundedToProduct_apply_coord] at hcoord
  exact hcoord

lemma boundedRealToProductReal_shortExact :
    (ShortComplex.mk boundedRealToProductReal (cokernel.π boundedRealToProductReal)
      (cokernel.condition boundedRealToProductReal)).ShortExact := by
  exact ⟨ShortComplex.exact_cokernel boundedRealToProductReal⟩

lemma boundedToProduct_shortExact :
    (ShortComplex.mk boundedToProduct (cokernel.π boundedToProduct)
      (cokernel.condition boundedToProduct)).ShortExact := by
  exact ⟨ShortComplex.exact_cokernel boundedToProduct⟩

lemma hom_cokernel_boundedRealToProductReal_solid_eq_zero
    (E : Solid) (f : cokernel boundedRealToProductReal ⟶ (isSolid.ι).obj E) :
    f = 0 := by
  have h : cokernel.π boundedRealToProductReal ≫ f = 0 :=
    hom_eq_zero_of_dyadicContractible productRealSequences E
      (cokernel.π boundedRealToProductReal ≫ f)
  have h' : cokernel.π boundedRealToProductReal ≫ f =
      cokernel.π boundedRealToProductReal ≫ 0 := by
    rw [comp_zero]
    exact h
  exact (cancel_epi (cokernel.π boundedRealToProductReal)).1 h'

lemma ext1_cokernel_boundedRealToProductReal_solid_eq_zero
    (E : Solid) (α : Abelian.Ext (cokernel boundedRealToProductReal)
      ((isSolid.ι).obj E) 1) :
    α = 0 := by
  let S := ShortComplex.mk boundedRealToProductReal (cokernel.π boundedRealToProductReal)
    (cokernel.condition boundedRealToProductReal)
  have hS : S.ShortExact := boundedRealToProductReal_shortExact
  let Y : LightCondAb := (isSolid.ι).obj E
  have hpre : (Ext.mk₀ (cokernel.π boundedRealToProductReal)).comp α (zero_add 1) = 0 :=
    ext1_eq_zero_of_dyadicContractible productRealSequences E
      ((Ext.mk₀ (cokernel.π boundedRealToProductReal)).comp α (zero_add 1))
  rcases Ext.contravariant_sequence_exact₃ hS Y α hpre (n₀ := 0) (by simp) with ⟨β, hβ⟩
  have hβzero : β = 0 := ext0_eq_zero_of_dyadicContractible boundedRealSequences E β
  rw [← hβ, hβzero]
  simp

private lemma isZero_solidification_of_solid_hom_zero (Q : LightCondAb)
    (hQ : ∀ E : Solid, ∀ f : Q ⟶ (isSolid.ι).obj E, f = 0) :
    IsZero (solidification.obj Q) := by
  rw [IsZero.iff_id_eq_zero]
  let E : Solid := solidification.obj Q
  have hzero : solidificationAdjunction.homEquiv Q E (𝟙 E) = 0 :=
    hQ E (solidificationAdjunction.homEquiv Q E (𝟙 E))
  apply (solidificationAdjunction.homEquiv Q E).injective
  rw [hzero]
  rw [Adjunction.homAddEquiv_zero]

/-- Lean's `IsZero` is not a typeclass; see `instIsZero_solidification_realCondensedAb`. -/
lemma instIsZero_solidification_cokernel_boundedRealToProductReal :
    IsZero (solidification.obj (cokernel boundedRealToProductReal)) :=
  isZero_solidification_of_solid_hom_zero (cokernel boundedRealToProductReal)
    hom_cokernel_boundedRealToProductReal_solid_eq_zero

lemma hom_cokernel_boundedToProduct_solid_eq_zero
    (E : Solid) (f : cokernel boundedToProduct ⟶ (isSolid.ι).obj E) :
    f = 0 := by
  let e := productIntQuotientIsoRealQuotient
  have h : e.inv ≫ f = 0 :=
    hom_cokernel_boundedRealToProductReal_solid_eq_zero E (e.inv ≫ f)
  calc
    f = e.hom ≫ (e.inv ≫ f) := by simp [e]
    _ = 0 := by rw [h, comp_zero]

lemma ext1_cokernel_boundedToProduct_solid_eq_zero
    (E : Solid) (α : Abelian.Ext (cokernel boundedToProduct)
      ((isSolid.ι).obj E) 1) :
    α = 0 := by
  let e := productIntQuotientIsoRealQuotient
  let β : Abelian.Ext (cokernel boundedRealToProductReal) ((isSolid.ι).obj E) 1 :=
    (Ext.mk₀ e.inv).comp α (zero_add 1)
  have hβ : β = 0 := ext1_cokernel_boundedRealToProductReal_solid_eq_zero E β
  have hα : (Ext.mk₀ e.hom).comp β (zero_add 1) = α := by
    dsimp [β]
    rw [Ext.mk₀_comp_mk₀_assoc]
    simp [e]
  rw [← hα, hβ]
  rw [Ext.comp_zero]

/-- Lean's `IsZero` is not a typeclass; see `instIsZero_solidification_realCondensedAb`. -/
lemma instIsZero_solidification_cokernel_boundedToProduct :
    IsZero (solidification.obj (cokernel boundedToProduct)) :=
  isZero_solidification_of_solid_hom_zero (cokernel boundedToProduct)
    hom_cokernel_boundedToProduct_solid_eq_zero

/-- A morphism of light condensed abelian groups is a solidification equivalence if restriction
along it gives bijections on maps to every solid target. -/
def IsSolidificationEquivalence {A B : LightCondAb} (f : A ⟶ B) : Prop :=
  ∀ E : Solid, Function.Bijective
    (fun g : B ⟶ (isSolid.ι).obj E => f ≫ g)

lemma isIso_solidification_map_of_isSolidificationEquivalence
    {A B : LightCondAb} (f : A ⟶ B)
    (hf : IsSolidificationEquivalence f) :
    IsIso (solidification.map f) := by
  apply isIso_of_coyoneda_map_bijective
  intro E
  let eA := solidificationAdjunction.homEquiv A E
  let eB := solidificationAdjunction.homEquiv B E
  let φ : (solidification.obj B ⟶ E) ≃ (B ⟶ (isSolid.ι).obj E) := eB
  let ψ : (solidification.obj A ⟶ E) ≃ (A ⟶ (isSolid.ι).obj E) := eA
  have hcompat : ∀ g : solidification.obj B ⟶ E,
      ψ (solidification.map f ≫ g) = f ≫ φ g := by
    intro g
    exact solidificationAdjunction.homEquiv_naturality_left f g
  constructor
  · intro g h hgh
    apply φ.injective
    apply (hf E).1
    simpa only [hcompat] using congrArg ψ hgh
  · intro h
    rcases (hf E).2 (ψ h) with ⟨g, hg⟩
    refine ⟨φ.symm g, ?_⟩
    apply ψ.injective
    simpa only [hcompat, Equiv.apply_symm_apply] using hg

lemma isSolidificationEquivalence_of_mono_cokernel_ext01
    {A B : LightCondAb} (f : A ⟶ B) [Mono f]
    (hHom : ∀ E : Solid, ∀ q : cokernel f ⟶ (isSolid.ι).obj E, q = 0)
    (hExt : ∀ E : Solid, ∀ α : Abelian.Ext (cokernel f) ((isSolid.ι).obj E) 1,
      α = 0) :
    IsSolidificationEquivalence f := by
  intro E
  let Y : LightCondAb := (isSolid.ι).obj E
  constructor
  · intro g h hgh
    have hdiff : f ≫ (g - h) = 0 := by
      rw [Preadditive.comp_sub]
      exact sub_eq_zero.mpr hgh
    have hfactor : cokernel.π f ≫ cokernel.desc f (g - h) hdiff = g - h :=
      cokernel.π_desc f (g - h) hdiff
    have hzero : cokernel.desc f (g - h) hdiff = 0 := hHom E _
    have hdiffzero : g - h = 0 := by
      rw [← hfactor, hzero, comp_zero]
    exact sub_eq_zero.mp hdiffzero
  · intro a
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel f⟩
    have hδ : hS.extClass.comp (Ext.mk₀ a) (rfl : 1 + 0 = 1) = 0 :=
      hExt E (hS.extClass.comp (Ext.mk₀ a) (rfl : 1 + 0 = 1))
    rcases Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ a) (rfl : 1 + 0 = 1) hδ
      with ⟨β, hβ⟩
    rcases (Ext.mk₀_bijective B Y).2 β with ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    simp only [Ext.mk₀_comp_mk₀] at hβ
    exact (Ext.mk₀_bijective A Y).1 hβ

lemma boundedToProduct_isSolidificationEquivalence :
    IsSolidificationEquivalence boundedToProduct :=
  isSolidificationEquivalence_of_mono_cokernel_ext01 boundedToProduct
    hom_cokernel_boundedToProduct_solid_eq_zero
    ext1_cokernel_boundedToProduct_solid_eq_zero

instance instIsIso_solidification_map_boundedToProduct :
    IsIso (solidification.map boundedToProduct) :=
  isIso_solidification_map_of_isSolidificationEquivalence boundedToProduct
    boundedToProduct_isSolidificationEquivalence

/-- The counit isomorphism identifying the solidification of a solid object with itself. -/
noncomputable def solidificationObjValIso (A : Solid) :
    solidification.obj ((isSolid.ι).obj A) ≅ A := by
  haveI : IsIso solidificationAdjunction.counit := inferInstance
  exact (asIso solidificationAdjunction.counit).app A

/-- The solidification of bounded integer sequences is the solid product of countably many
copies of `ℤ`. -/
noncomputable def solidBoundedIsoProduct :
    solidification.obj boundedIntSequences ≅ productInt :=
  asIso (solidification.map boundedToProduct) ≪≫ solidificationObjValIso productInt

lemma solidBoundedIsoProduct_hom_eq :
    solidBoundedIsoProduct.hom =
      (asIso (solidification.map boundedToProduct)).hom ≫
        (solidificationObjValIso productInt).hom :=
  rfl

end ProjectiveGeneratorProof
end Solid
end LightCondensed
