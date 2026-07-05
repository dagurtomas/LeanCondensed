/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Projects.SolidProjectiveGenerator.PBasisTensorDesc
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
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

end ProjectiveGeneratorProof
end Solid
end LightCondensed
