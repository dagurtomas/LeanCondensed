/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Projects.SolidProjectiveGenerator.PBasisTensorDesc
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.LeftExact
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
    have hGzero : (Ext.mk₀ (MonoidalClosed.curry (q - r))).comp hGS.extClass (zero_add 1) = 0 := by
      change (Ext.mk₀ dqr).comp hGS.extClass (zero_add 1) = 0
      have htmp := congrArg (fun z => z.comp (Ext.mk₀ (inv φS.τ₁)) (add_zero 1)) hGσzero
      simpa [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using htmp
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
    dsimp [γ, δGq]
    simp [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end ExtOne

/-- The SPG12b statement in degree `1`: precomposition by `(oneMinusShift ℤ) ▷ X` is
bijective on `Ext¹` for every solid target. -/
lemma ext1_precomp_oneMinusShift_tensor_bijective
    (X : LightCondAb) (E : Solid) :
    Function.Bijective
      (fun α : Ext (P ℤ ⊗ X) ((isSolid.ι).obj E) 1 =>
        (Ext.mk₀ ((oneMinusShift ℤ) ▷ X)).comp α (zero_add 1)) :=
  ExtOne.ext1_precomp_oneMinusShift_tensor_bijective X E

end ProjectiveGeneratorProof
end Solid
end LightCondensed
