import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.Projects.Sequence
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.InternallyProjective
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic

/-!
# Algebra for the proof that `ℤ` is solid

This file contains the finite-support sequence calculation used in the proof that the light
condensed abelian group of integers is solid.  The finite-difference operator
`a ↦ (fun n => a n - a (n + 1))` is an automorphism of finitely supported integer sequences, with
inverse given by finite tail sums.
-/

open scoped BigOperators

noncomputable section

open CategoryTheory LightCondensed LightProfinite OnePoint MonoidalCategory MonoidalClosed Limits
  Filter Topology

namespace LightCondensed.Solid.IntProof

/-- The discrete light condensed abelian group `ℤ`. -/
abbrev Zdisc : LightCondAb :=
  (discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- Finitely supported integer sequences. -/
abbrev SeqZ := ℕ →₀ ℤ

/-- Left shift of finitely supported sequences: `(aₙ) ↦ (aₙ₊₁)`. -/
def seqShift : SeqZ →ₗ[ℤ] SeqZ :=
  (Finsupp.comapDomain.addMonoidHom (f := fun n : ℕ => n + 1) (by
    intro a b h
    exact Nat.succ.inj h)).toIntLinearMap

@[simp]
lemma seqShift_apply (a : SeqZ) (n : ℕ) :
    seqShift a n = a (n + 1) := by
  simp [seqShift, Finsupp.comapDomain_apply]

/-- Finite difference of finitely supported sequences: `(aₙ) ↦ (aₙ - aₙ₊₁)`. -/
def seqDiff : SeqZ →ₗ[ℤ] SeqZ :=
  LinearMap.id - seqShift

@[simp]
lemma seqDiff_apply (a : SeqZ) (n : ℕ) :
    seqDiff a n = a n - a (n + 1) := by
  simp [seqDiff]

/-- The finite tail sum function underlying `seqTailSum`. -/
def tailFun (b : SeqZ) (n : ℕ) : ℤ :=
  b.sum fun i z => if n ≤ i then z else 0

lemma tailFun_eq_sum_filter (b : SeqZ) (n : ℕ) :
    tailFun b n = ∑ i ∈ b.support.filter (fun i => n ≤ i), b i := by
  simp [tailFun, Finsupp.sum, Finset.sum_filter]

/-- Tail sums of finitely supported sequences, as an additive homomorphism. -/
def seqTailSumAddHom : SeqZ →+ SeqZ where
  toFun b :=
    Finsupp.onFinset (b.support.biUnion fun i => Finset.range (i + 1))
      (fun n => tailFun b n)
      (by
        intro n hn
        by_contra hmem
        have hzero : tailFun b n = 0 := by
          rw [tailFun_eq_sum_filter]
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_filter] at hi
          have : n ∈ b.support.biUnion (fun i => Finset.range (i + 1)) := by
            rw [Finset.mem_biUnion]
            refine ⟨i, hi.1, ?_⟩
            rw [Finset.mem_range]
            omega
          exact False.elim (hmem this)
        exact hn hzero)
  map_zero' := by
    ext n
    simp [tailFun]
  map_add' b c := by
    ext n
    simp only [Finsupp.coe_onFinset]
    dsimp [tailFun]
    rw [Finsupp.sum_add_index']
    · intro i
      by_cases h : n ≤ i <;> simp [h]
    · intro i x y
      by_cases h : n ≤ i <;> simp [h]

/-- Tail sums of finitely supported sequences. -/
def seqTailSum : SeqZ →ₗ[ℤ] SeqZ :=
  seqTailSumAddHom.toIntLinearMap

@[simp]
lemma seqTailSum_apply (b : SeqZ) (n : ℕ) :
    seqTailSum b n = ∑ i ∈ b.support.filter (fun i => n ≤ i), b i := by
  change tailFun b n = _
  exact tailFun_eq_sum_filter b n

lemma filter_ge_eq_insert_filter_gt (b : SeqZ) {n : ℕ} (hn : n ∈ b.support) :
    b.support.filter (fun i => n ≤ i) = insert n (b.support.filter (fun i => n < i)) := by
  ext i
  by_cases hin : i = n
  · subst i
    simp [hn]
  · simp [hin]
    intro _
    constructor <;> intro hi <;> omega

lemma filter_ge_eq_filter_gt (b : SeqZ) {n : ℕ} (hn : n ∉ b.support) :
    b.support.filter (fun i => n ≤ i) = b.support.filter (fun i => n < i) := by
  ext i
  by_cases hin : i = n
  · subst i
    simp [hn]
  · simp
    intro _
    constructor <;> intro hi <;> omega

lemma tailFun_sub_succ (b : SeqZ) (n : ℕ) :
    tailFun b n - tailFun b (n + 1) = b n := by
  rw [tailFun_eq_sum_filter, tailFun_eq_sum_filter]
  simp only [Nat.add_one_le_iff]
  by_cases hn : n ∈ b.support
  · rw [filter_ge_eq_insert_filter_gt b hn]
    rw [Finset.sum_insert]
    · abel
    · simp
  · rw [filter_ge_eq_filter_gt b hn]
    rw [Finsupp.notMem_support_iff.mp hn]
    abel

lemma seqDiff_seqTailSum (b : SeqZ) :
    seqDiff (seqTailSum b) = b := by
  ext n
  simp only [seqDiff_apply, seqTailSum_apply]
  rw [← tailFun_eq_sum_filter, ← tailFun_eq_sum_filter, tailFun_sub_succ]

lemma seqDiff_eq_zero {a : SeqZ} (h : seqDiff a = 0) : a = 0 := by
  by_contra ha
  obtain ⟨N, hN⟩ := Finsupp.support_nonempty_iff.mpr ha
  let M := a.support.max' ⟨N, hN⟩
  have hM : M ∈ a.support := Finset.max'_mem _ _
  have hMsucc : M + 1 ∉ a.support := by
    intro hmem
    have hle := Finset.le_max' a.support (M + 1) hmem
    omega
  have heval : seqDiff a M = (0 : SeqZ) M := by rw [h]
  simp [Finsupp.notMem_support_iff.mp hMsucc] at heval
  exact Finsupp.mem_support_iff.mp hM heval

lemma seqTailSum_seqDiff (a : SeqZ) :
    seqTailSum (seqDiff a) = a := by
  have hzero : seqDiff (seqTailSum (seqDiff a) - a) = 0 := by
    calc
      seqDiff (seqTailSum (seqDiff a) - a)
          = seqDiff (seqTailSum (seqDiff a)) - seqDiff a := by simp
      _ = seqDiff a - seqDiff a := by rw [seqDiff_seqTailSum]
      _ = 0 := by simp
  have h := seqDiff_eq_zero hzero
  exact sub_eq_zero.mp h

/-- Finite difference is an automorphism of finitely supported integer sequences. -/
noncomputable def seqDiffEquiv : SeqZ ≃ₗ[ℤ] SeqZ where
  toLinearMap := seqDiff
  invFun := seqTailSum
  left_inv := seqTailSum_seqDiff
  right_inv := seqDiff_seqTailSum

example : Function.Bijective seqDiff :=
  seqDiffEquiv.bijective

/-- Pointwise finite difference is an automorphism of locally constant families of finitely
supported integer sequences. -/
noncomputable def locallyConstantSeqDiffEquiv (S : LightProfinite) :
    LocallyConstant S SeqZ ≃ LocallyConstant S SeqZ where
  toFun := LocallyConstant.map seqDiff
  invFun := LocallyConstant.map seqTailSum
  left_inv g := by
    ext s n
    simp [LocallyConstant.map, seqTailSum_seqDiff]
  right_inv g := by
    ext s n
    simp [LocallyConstant.map, seqDiff_seqTailSum]

section InternalHomPoints

variable {R : Type} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- On `S`-points of internal Homs, precomposition by `f` is precomposition by
`f ▷ ℤ[S]` after applying `ihomPoints`. -/
lemma ihom_pre_val_app
    {A B X : LightCondMod R} (f : B ⟶ A)
    (S : LightProfinite)
    (x : ((ihom A).obj X).obj.obj ⟨S⟩) :
    (((MonoidalClosed.pre f).app X).hom.app ⟨S⟩) x =
      (ihomPoints R B X S).symm
        ((f ▷ (LightCondensed.free R).obj S.toCondensed) ≫ ihomPoints R A X S x) := by
  apply (ihomPoints R B X S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_pre_app,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

lemma ihomPoints_pre_app
    {A B X : LightCondMod R} (f : B ⟶ A)
    (S : LightProfinite)
    (x : ((ihom A).obj X).obj.obj ⟨S⟩) :
    ihomPoints R B X S
      ((((MonoidalClosed.pre f).app X).hom.app ⟨S⟩) x)
      = (f ▷ (LightCondensed.free R).obj S.toCondensed) ≫ ihomPoints R A X S x := by
  rw [ihom_pre_val_app]
  simp

end InternalHomPoints

section FreeDiscrete

variable (R : Type) [Ring R]
variable (T : LightProfinite) (M : ModuleCat R)

/-- Maps from the free light condensed `R`-module on a light profinite set `T` to a discrete
module `M` are locally constant `M`-valued functions on `T`. -/
noncomputable def freeHomDiscreteEquiv :
    ((LightCondensed.free R).obj T.toCondensed ⟶ (LightCondensed.discrete (ModuleCat R)).obj M) ≃
      LocallyConstant T M where
  toFun f := by
    let g : T.toCondensed ⟶
        (LightCondensed.forget R).obj ((LightCondensed.discrete (ModuleCat R)).obj M) :=
      (LightCondensed.freeForgetAdjunction R).homEquiv T.toCondensed
        ((LightCondensed.discrete (ModuleCat R)).obj M) f
    let g' : T.toCondensed ⟶
        (LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M) :=
      g ≫ (LightCondensed.forget R).map
        ((LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M)
    let x := (coherentTopology LightProfinite).yonedaEquiv g'
    change LocallyConstant T M at x
    exact x
  invFun x := by
    let x' : ((LightCondensed.forget R).obj
        ((LightCondMod.LocallyConstant.functor R).obj M)).obj.obj ⟨T⟩ := x
    let g' : T.toCondensed ⟶
        (LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M) :=
      (coherentTopology LightProfinite).yonedaEquiv.symm x'
    let g : T.toCondensed ⟶
        (LightCondensed.forget R).obj ((LightCondensed.discrete (ModuleCat R)).obj M) :=
      g' ≫ (LightCondensed.forget R).map
        ((LightCondMod.LocallyConstant.functorIsoDiscrete R).hom.app M)
    exact ((LightCondensed.freeForgetAdjunction R).homEquiv T.toCondensed
      ((LightCondensed.discrete (ModuleCat R)).obj M)).symm g
  left_inv f := by simp
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
lemma freeHomDiscreteEquiv_map {T T' : LightProfinite} (φ : T' ⟶ T)
    (f : (LightCondensed.free R).obj T.toCondensed ⟶
      (LightCondensed.discrete (ModuleCat R)).obj M) :
    freeHomDiscreteEquiv R T' M
        ((LightCondensed.free R).map (lightProfiniteToLightCondSet.map φ) ≫ f) =
      (freeHomDiscreteEquiv R T M f).comap φ.hom.hom := by
  change (freeHomDiscreteEquiv R T' M
        ((LightCondensed.free R).map (lightProfiniteToLightCondSet.map φ) ≫ f) :
      ((LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M)).obj.obj
        ⟨T'⟩) =
    (((LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M)).obj.map
        φ.op)
      (freeHomDiscreteEquiv R T M f :
        ((LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M)).obj.obj
          ⟨T⟩)
  apply (((coherentTopology LightProfinite).yonedaEquiv (X := T')
    (F := (LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M))).symm.injective)
  dsimp [freeHomDiscreteEquiv]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Equiv.symm_apply_apply]
  let m : T.toCondensed ⟶
      (LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M) :=
    ((LightCondensed.freeForgetAdjunction R).homEquiv T.toCondensed
      ((LightCondensed.discrete (ModuleCat R)).obj M)) f ≫
      (LightCondensed.forget R).map ((LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M)
  change (coherentTopology LightProfinite).yoneda.map φ ≫ m =
    (coherentTopology LightProfinite).yonedaEquiv.symm
      ((((LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M)).obj.map
          φ.op) ((coherentTopology LightProfinite).yonedaEquiv m))
  simpa using (GrothendieckTopology.yonedaEquiv_symm_map (J := coherentTopology LightProfinite)
    (f := φ.op)
    (F := (LightCondensed.forget R).obj ((LightCondMod.LocallyConstant.functor R).obj M))
    (t := (coherentTopology LightProfinite).yonedaEquiv m)).symm

set_option backward.isDefEq.respectTransparency false in
lemma freeHomDiscreteEquiv_zero_apply (x : T) :
    freeHomDiscreteEquiv R T M
      (0 : (LightCondensed.free R).obj T.toCondensed ⟶
        (LightCondensed.discrete (ModuleCat R)).obj M) x = 0 := by
  dsimp [freeHomDiscreteEquiv]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  let y := ((ConcreteCategory.hom
    (((LightCondensed.freeForgetAdjunction R).unit.app T.toCondensed).hom.app (Opposite.op T)))
      (𝟙 T))
  have hy : (ConcreteCategory.hom (((LightCondensed.forget R).map
        (0 : (LightCondensed.free R).obj T.toCondensed ⟶
          (LightCondensed.discrete (ModuleCat R)).obj M)).hom.app (Opposite.op T))) y =
      (0 : ((LightCondensed.discrete (ModuleCat R)).obj M).obj.obj (Opposite.op T)) := by
    change ((0 : (LightCondensed.free R).obj T.toCondensed ⟶
      (LightCondensed.discrete (ModuleCat R)).obj M).hom.app (Opposite.op T)) y = 0
    simp
  let z : LocallyConstant T M :=
    ((((LightCondensed.forget R).map
      ((LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M)).hom.app (Opposite.op T))
        ((((LightCondensed.forget R).map
          (0 : (LightCondensed.free R).obj T.toCondensed ⟶
            (LightCondensed.discrete (ModuleCat R)).obj M)).hom.app (Opposite.op T)) y))
  change z x = 0
  rw [show z = (((LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M).hom.app
      (Opposite.op T))
        ((((LightCondensed.forget R).map
          (0 : (LightCondensed.free R).obj T.toCondensed ⟶
            (LightCondensed.discrete (ModuleCat R)).obj M)).hom.app (Opposite.op T)) y) from rfl]
  rw [hy]
  let w : ((LightCondMod.LocallyConstant.functor R).obj M).obj.obj (Opposite.op T) :=
    (((LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M).hom.app (Opposite.op T))
      (0 : ((LightCondensed.discrete (ModuleCat R)).obj M).obj.obj (Opposite.op T))
  change (show LocallyConstant T M from w) x = 0
  simp [w]

set_option backward.isDefEq.respectTransparency false in
lemma freeHomDiscreteEquiv_sub_apply
    (f g : (LightCondensed.free R).obj T.toCondensed ⟶
      (LightCondensed.discrete (ModuleCat R)).obj M)
    (x : T) :
    freeHomDiscreteEquiv R T M (f - g) x =
      freeHomDiscreteEquiv R T M f x - freeHomDiscreteEquiv R T M g x := by
  dsimp [freeHomDiscreteEquiv]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  let y := ((ConcreteCategory.hom
    (((LightCondensed.freeForgetAdjunction R).unit.app T.toCondensed).hom.app (Opposite.op T)))
      (𝟙 T))
  let Fiso := (LightCondMod.LocallyConstant.functorIsoDiscrete R).inv.app M
  change (show LocallyConstant T M from Fiso.hom.app (Opposite.op T)
      (((f - g).hom.app (Opposite.op T)) y)) x =
    (show LocallyConstant T M from Fiso.hom.app (Opposite.op T)
      ((f.hom.app (Opposite.op T)) y)) x -
    (show LocallyConstant T M from Fiso.hom.app (Opposite.op T)
      ((g.hom.app (Opposite.op T)) y)) x
  have hfg : (((f - g).hom.app (Opposite.op T)) y) =
      ((f.hom.app (Opposite.op T)) y) - ((g.hom.app (Opposite.op T)) y) := by
    rfl
  rw [hfg]
  have hF : Fiso.hom.app (Opposite.op T)
        (((f.hom.app (Opposite.op T)) y) - ((g.hom.app (Opposite.op T)) y)) =
      Fiso.hom.app (Opposite.op T) ((f.hom.app (Opposite.op T)) y) -
        Fiso.hom.app (Opposite.op T) ((g.hom.app (Opposite.op T)) y) := by
    exact (Fiso.hom.app (Opposite.op T)).hom.map_sub _ _
  rw [hF]
  rfl

end FreeDiscrete

/-- The product test object `(ℕ∪{∞}) × S`, written in the cartesian monoidal structure on
`LightProfinite`. -/
abbrev NinfTensor (S : LightProfinite) : LightProfinite :=
  (ℕ∪{∞} : LightProfinite) ⊗ S

section CokernelAndFreeTensor

set_option backward.isDefEq.respectTransparency false in
/-- Local copy of the cokernel/tensor isomorphism, avoiding an import cycle with `LightSolid`. -/
noncomputable def tensorCokerIsoInt {A B C : LightCondAb} (f : A ⟶ B) :
    cokernel f ⊗ C ≅ cokernel (f ▷ C) := by
  letI : PreservesColimits (tensorRight C) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight C)
  exact preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

/-- Maps out of a cokernel are maps out of the numerator that kill the denominator. -/
noncomputable def cokernelHomEquiv {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B X : C} (f : A ⟶ B) [HasCokernel f] :
    (cokernel f ⟶ X) ≃ {g : B ⟶ X // f ≫ g = 0} where
  toFun k := ⟨cokernel.π f ≫ k, by simp⟩
  invFun g := cokernel.desc f g.1 g.2
  left_inv k := by
    apply Cofork.IsColimit.hom_ext (cokernelIsCokernel f)
    change cokernel.π f ≫ cokernel.desc f (cokernel.π f ≫ k) _ = cokernel.π f ≫ k
    rw [cokernel.π_desc]
  right_inv g := by
    ext
    simp

/-- Tensor product of two free light condensed abelian groups as the free object on the product. -/
noncomputable def freeTensorIsoInt (S T : LightProfinite) :
    (free ℤ).obj S.toCondensed ⊗ (free ℤ).obj T.toCondensed ≅
      (free ℤ).obj (S ⊗ T).toCondensed :=
  Functor.Monoidal.μIso (free ℤ) S.toCondensed T.toCondensed ≪≫
    (free ℤ).mapIso (Functor.Monoidal.μIso lightProfiniteToLightCondSet S T)

/-- Maps out of a tensor product of two free light condensed abelian groups as locally constant
integer-valued functions on the product. -/
noncomputable def freeProductHomEquiv (A S : LightProfinite) :
    (((free ℤ).obj A.toCondensed) ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc) ≃
      LocallyConstant (A ⊗ S : LightProfinite) ℤ :=
  (Iso.homCongr (freeTensorIsoInt A S) (Iso.refl Zdisc)).trans
    (freeHomDiscreteEquiv ℤ (A ⊗ S : LightProfinite) (ModuleCat.of ℤ ℤ))

@[reassoc]
lemma freeTensorIsoInt_inv_naturality_left {A' A S : LightProfinite} (φ : A' ⟶ A) :
    (freeTensorIsoInt A' S).inv ≫
        ((free ℤ).map (lightProfiniteToLightCondSet.map φ) ▷ (free ℤ).obj S.toCondensed) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (φ ⊗ₘ 𝟙 S)) ≫
        (freeTensorIsoInt A S).inv := by
  dsimp [freeTensorIsoInt]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_left]
  simp only [← Functor.map_comp_assoc]
  rw [Functor.OplaxMonoidal.δ_natural_left]
  simp [MonoidalCategory.tensorHom_id]

set_option backward.isDefEq.respectTransparency false in
lemma freeProductHomEquiv_precomp_left {A' A S : LightProfinite} (φ : A' ⟶ A)
    (g : ((free ℤ).obj A.toCondensed ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc)) :
    freeProductHomEquiv A' S
        (((free ℤ).map (lightProfiniteToLightCondSet.map φ) ▷
            (free ℤ).obj S.toCondensed) ≫ g) =
      (freeProductHomEquiv A S g).comap (φ ⊗ₘ 𝟙 S).hom.hom := by
  dsimp [freeProductHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  have hcomp : (freeTensorIsoInt A' S).inv ≫
        (((free ℤ).map (lightProfiniteToLightCondSet.map φ) ▷
          (free ℤ).obj S.toCondensed) ≫ g) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (φ ⊗ₘ 𝟙 S)) ≫
        ((freeTensorIsoInt A S).inv ≫ g) := by
    rw [← Category.assoc, freeTensorIsoInt_inv_naturality_left, Category.assoc]
  rw [hcomp]
  rw [freeHomDiscreteEquiv_map]

lemma freeProductHomEquiv_zero_apply (A S : LightProfinite) (x : (A ⊗ S : LightProfinite)) :
    freeProductHomEquiv A S
      (0 : (free ℤ).obj A.toCondensed ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc) x = 0 := by
  dsimp [freeProductHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  simpa using freeHomDiscreteEquiv_zero_apply ℤ (A ⊗ S : LightProfinite)
    (ModuleCat.of ℤ ℤ) x

/-- Maps out of the free numerator `(ℕ∪{∞}) × S` are locally constant integer-valued functions. -/
noncomputable def numeratorHomEquiv (S : LightProfinite) :
    ((((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) ≃
      LocallyConstant (NinfTensor S) ℤ :=
  freeProductHomEquiv (ℕ∪{∞}) S

/-- Maps out of `P ℤ ⊗ ℤ[S]` as numerator maps satisfying the cokernel relation. -/
noncomputable def pTensorHomSubtypeEquiv (S : LightProfinite) :
    ((P ℤ ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) ≃
      {g : (((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc) //
        (P_map ℤ ▷ (free ℤ).obj S.toCondensed) ≫ g = 0} := by
  let C := (free ℤ).obj S.toCondensed
  let e : P ℤ ⊗ C ≅ cokernel (P_map ℤ ▷ C) := tensorCokerIsoInt (P_map ℤ)
  exact (Iso.homCongr e (Iso.refl Zdisc)).trans (cokernelHomEquiv (P_map ℤ ▷ C))

set_option backward.isDefEq.respectTransparency false in
lemma tensorCokerIsoInt_π_inv {C : LightCondAb} :
    cokernel.π (P_map ℤ ▷ C) ≫
        (tensorCokerIsoInt (P_map ℤ) : P ℤ ⊗ C ≅ cokernel (P_map ℤ ▷ C)).inv =
      P_proj ℤ ▷ C := by
  simp [tensorCokerIsoInt, P_proj]
  change 𝟙 ((free ℤ).obj (ℕ∪{∞}).toCondensed ⊗ C) ≫ P_proj ℤ ▷ C = P_proj ℤ ▷ C
  rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
lemma pTensorHomSubtypeEquiv_apply_coe (S : LightProfinite)
    (f : (P ℤ ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) :
    (pTensorHomSubtypeEquiv S f).1 = (P_proj ℤ ▷ (free ℤ).obj S.toCondensed) ≫ f := by
  dsimp [pTensorHomSubtypeEquiv, cokernelHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  simpa [Category.assoc] using congrArg (fun k => k ≫ f)
    (tensorCokerIsoInt_π_inv (C := (free ℤ).obj S.toCondensed))

lemma freeProductHomEquiv_sub_apply (A S : LightProfinite)
    (f g : (free ℤ).obj A.toCondensed ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc)
    (x : (A ⊗ S : LightProfinite)) :
    freeProductHomEquiv A S (f - g) x =
      freeProductHomEquiv A S f x - freeProductHomEquiv A S g x := by
  dsimp [freeProductHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [Preadditive.comp_sub]
  exact freeHomDiscreteEquiv_sub_apply ℤ (A ⊗ S : LightProfinite) (ModuleCat.of ℤ ℤ)
    ((freeTensorIsoInt A S).inv ≫ f) ((freeTensorIsoInt A S).inv ≫ g) x

lemma sub_whiskerRight {X Y C : LightCondAb} (f g : X ⟶ Y) :
    (f - g) ▷ C = f ▷ C - g ▷ C := by
  change (tensorRight C).map (f - g) = (tensorRight C).map f - (tensorRight C).map g
  exact Functor.map_sub (F := tensorRight C) (f := f) (g := g)

end CokernelAndFreeTensor

section VanishingAtInfinity

/-- Locally constant integer-valued functions on `(ℕ∪{∞}) × S` vanishing along `{∞} × S`. -/
abbrev VanishAtInfinity (S : LightProfinite) :=
  { h : LocallyConstant (NinfTensor S) ℤ // ∀ s : S, h (∞, s) = 0 }

lemma vanish_supportN_finite {S : LightProfinite} (h : VanishAtInfinity S) :
    Set.Finite {n : ℕ | ∃ s : S, h.1 ((n : ℕ∪{∞}), s) ≠ 0} := by
  let K : Set (NinfTensor S) := {x | h.1 x ≠ 0}
  have hKclosed : IsClosed K := by
    exact (isClosed_discrete ({z : ℤ | z ≠ 0})).preimage h.1.continuous
  have hKcompact : IsCompact K := by
    exact IsCompact.of_isClosed_subset isCompact_univ hKclosed (by intro x _; trivial)
  let L : Set ℕ∪{∞} := Prod.fst '' K
  have hLcompact : IsCompact L := hKcompact.image continuous_fst
  have hLnot : (∞ : ℕ∪{∞}) ∉ L := by
    rintro ⟨x, hxK, hx⟩
    rcases x with ⟨a, s⟩
    dsimp [K] at hxK
    dsimp at hx
    subst hx
    exact hxK (h.2 s)
  have hLclosed : IsClosed L := hLcompact.isClosed
  have hprecompact : IsCompact (((↑) : ℕ → ℕ∪{∞}) ⁻¹' L) := by
    exact ((OnePoint.isClosed_iff_of_notMem (s := L) hLnot).mp hLclosed).2
  have hfinite : Set.Finite (((↑) : ℕ → ℕ∪{∞}) ⁻¹' L) := by
    exact isCompact_iff_finite.mp hprecompact
  convert hfinite using 1
  ext n
  simp [L, K]
  constructor <;> rintro ⟨s, hs⟩ <;> exact ⟨s, hs⟩

lemma vanish_eventually_zero {S : LightProfinite} (h : VanishAtInfinity S) :
    ∃ N : ℕ, ∀ s : S, ∀ n : ℕ, N ≤ n → h.1 ((n : ℕ∪{∞}), s) = 0 := by
  obtain ⟨N, hN⟩ := (vanish_supportN_finite h).bddAbove
  refine ⟨N + 1, ?_⟩
  intro s n hn
  by_contra hne
  have hmem : n ∈ {n : ℕ | ∃ s : S, h.1 ((n : ℕ∪{∞}), s) ≠ 0} := ⟨s, hne⟩
  have := hN hmem
  omega

/-- Convert a function on a finite initial segment to a finitely supported sequence. -/
noncomputable def finFunToSeq (N : ℕ) (v : Fin N → ℤ) : SeqZ :=
  Finsupp.onFinset (Finset.range N)
    (fun n => if hn : n < N then v ⟨n, hn⟩ else 0)
    (by
      intro n hnzero
      by_cases hn : n < N
      · simpa [Finset.mem_range] using hn
      · simp [hn] at hnzero)

@[simp]
lemma finFunToSeq_apply_lt (N n : ℕ) (hn : n < N) (v : Fin N → ℤ) :
    finFunToSeq N v n = v ⟨n, hn⟩ := by
  simp [finFunToSeq, hn]

@[simp]
lemma finFunToSeq_apply_not_lt (N n : ℕ) (hn : ¬ n < N) (v : Fin N → ℤ) :
    finFunToSeq N v n = 0 := by
  simp [finFunToSeq, hn]

noncomputable def finitePointMap (S : LightProfinite) (n : ℕ) : C(S, NinfTensor S) where
  toFun s := ((n : ℕ∪{∞}), s)
  continuous_toFun := continuous_const.prodMk continuous_id

/-- A vanishing locally constant family on `(ℕ∪{∞}) × S` gives a locally constant
`S`-family of finitely supported sequences. -/
noncomputable def vanishToSeq {S : LightProfinite} (h : VanishAtInfinity S) :
    LocallyConstant S SeqZ := by
  let N := Classical.choose (vanish_eventually_zero h)
  let coords : Fin N → LocallyConstant S ℤ := fun i => h.1.comap (finitePointMap S i.1)
  exact (LocallyConstant.unflip coords).map (finFunToSeq N)

lemma vanishToSeq_apply {S : LightProfinite} (h : VanishAtInfinity S) (s : S) (n : ℕ) :
    vanishToSeq h s n = h.1 ((n : ℕ∪{∞}), s) := by
  dsimp [vanishToSeq]
  let N := Classical.choose (vanish_eventually_zero h)
  have hN := Classical.choose_spec (vanish_eventually_zero h)
  by_cases hn : n < N
  · simp [N, hn, finitePointMap, LocallyConstant.unflip, LocallyConstant.comap]
  · have hzero := hN s n (by omega)
    simp [N, hn, hzero]

noncomputable def truncIndexFun (N : ℕ) : ℕ∪{∞} → Option (Fin N)
  | ∞ => none
  | (OnePoint.some n) => if hn : n < N then Option.some ⟨n, hn⟩ else none

lemma truncIndexFun_eventually_none (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, truncIndexFun N (n : ℕ∪{∞}) = none := by
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  simp [truncIndexFun, not_lt.mpr hn]

/-- The locally constant map that remembers finite indices `< N` and collapses the tail and
`∞` to `none`. -/
noncomputable def truncIndex (N : ℕ) : LocallyConstant ℕ∪{∞} (Option (Fin N)) where
  toFun := truncIndexFun N
  isLocallyConstant := by
    letI : TopologicalSpace (Option (Fin N)) := ⊥
    haveI : DiscreteTopology (Option (Fin N)) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    rw [LightProfinite.continuous_iff_convergent]
    exact tendsto_nhds_of_eventually_eq (truncIndexFun_eventually_none N)

noncomputable def fstMap (S : LightProfinite) : C(NinfTensor S, ℕ∪{∞}) where
  toFun x := x.1
  continuous_toFun := continuous_fst

noncomputable def sndMap (S : LightProfinite) : C(NinfTensor S, S) where
  toFun x := x.2
  continuous_toFun := continuous_snd

lemma seq_family_support_finite {S : LightProfinite} (g : LocallyConstant S SeqZ) :
    Set.Finite {n : ℕ | ∃ s : S, g s n ≠ 0} := by
  let R : Set SeqZ := Set.range (fun s : S => g s)
  have hR : R.Finite := by simpa [R] using g.range_finite
  let U : Set ℕ := ⋃ a ∈ R, (a.support : Set ℕ)
  have hU : U.Finite := hR.biUnion (fun a _ => a.support.finite_toSet)
  apply hU.subset
  intro n hn
  rcases hn with ⟨s, hs⟩
  change n ∈ ⋃ a ∈ R, (a.support : Set ℕ)
  rw [Set.mem_iUnion]
  refine ⟨g s, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨⟨s, rfl⟩, by simpa [Finsupp.mem_support_iff] using hs⟩

lemma seq_family_eventually_zero {S : LightProfinite} (g : LocallyConstant S SeqZ) :
    ∃ N : ℕ, ∀ s : S, ∀ n : ℕ, N ≤ n → g s n = 0 := by
  obtain ⟨N, hN⟩ := (seq_family_support_finite g).bddAbove
  refine ⟨N + 1, ?_⟩
  intro s n hn
  by_contra hne
  have hmem : n ∈ {n : ℕ | ∃ s : S, g s n ≠ 0} := ⟨s, hne⟩
  have := hN hmem
  omega

/-- A locally constant `S`-family of finitely supported sequences gives a locally constant function
on `(ℕ∪{∞}) × S` that vanishes along `{∞} × S`. -/
noncomputable def seqToVanish {S : LightProfinite} (g : LocallyConstant S SeqZ) :
    VanishAtInfinity S := by
  let N := Classical.choose (seq_family_eventually_zero g)
  let idx : LocallyConstant (NinfTensor S) (Option (Fin N)) := (truncIndex N).comap (fstMap S)
  let fam : LocallyConstant (NinfTensor S) SeqZ := g.comap (sndMap S)
  refine ⟨⟨fun x => match idx x with | none => 0 | Option.some i => fam x i.1, ?_⟩, ?_⟩
  · exact idx.isLocallyConstant.comp₂ fam.isLocallyConstant fun oi a =>
      match oi with | none => 0 | Option.some i => a i.1
  · intro s
    simp [idx, truncIndex, truncIndexFun, fstMap]

lemma seqToVanish_apply_nat {S : LightProfinite} (g : LocallyConstant S SeqZ) (s : S) (n : ℕ) :
    (seqToVanish g).1 ((n : ℕ∪{∞}), s) = g s n := by
  dsimp [seqToVanish]
  let N := Classical.choose (seq_family_eventually_zero g)
  have hN := Classical.choose_spec (seq_family_eventually_zero g)
  by_cases hn : n < N
  · simp [N, hn, truncIndex, truncIndexFun, fstMap, sndMap]
  · have hzero := hN s n (by omega)
    simp [N, hn, truncIndex, truncIndexFun, fstMap, hzero]

lemma seqToVanish_apply_infty {S : LightProfinite} (g : LocallyConstant S SeqZ) (s : S) :
    (seqToVanish g).1 ((∞ : ℕ∪{∞}), s) = 0 := by
  exact (seqToVanish g).2 s

/-- Locally constant functions on `(ℕ∪{∞}) × S` vanishing at infinity are the same as locally
constant `S`-families of finitely supported integer sequences. -/
noncomputable def vanishAtInfinityEquiv (S : LightProfinite) :
    VanishAtInfinity S ≃ LocallyConstant S SeqZ where
  toFun := vanishToSeq
  invFun := seqToVanish
  left_inv h := by
    ext x
    rcases x with ⟨a, s⟩
    cases a using OnePoint.rec
    · rw [seqToVanish_apply_infty, h.2]
    · rw [seqToVanish_apply_nat, vanishToSeq_apply]
  right_inv g := by
    ext s n
    rw [vanishToSeq_apply, seqToVanish_apply_nat]

end VanishingAtInfinity

section PTensorHom

/-- The inclusion `{∞} × S → (ℕ∪{∞}) × S`. -/
noncomputable def iotaTensorMap (S : LightProfinite) :
    (LightProfinite.of PUnit.{1}) ⊗ S ⟶ NinfTensor S :=
  ι ⊗ₘ 𝟙 S

@[simp]
lemma iotaTensorMap_apply (S : LightProfinite) (s : S) :
    iotaTensorMap S (PUnit.unit, s) = ((∞ : ℕ∪{∞}), s) := rfl

/-- The cokernel relation on numerator maps is exactly vanishing along `{∞} × S`. -/
noncomputable def numeratorSubtypeVanishEquiv (S : LightProfinite) :
    {g : (((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj S.toCondensed ⟶ Zdisc) //
        (P_map ℤ ▷ (free ℤ).obj S.toCondensed) ≫ g = 0} ≃ VanishAtInfinity S where
  toFun q := by
    refine ⟨numeratorHomEquiv S q.1, ?_⟩
    intro s
    have hfun := congrArg (freeProductHomEquiv (LightProfinite.of PUnit.{1}) S) q.2
    dsimp [P_map] at hfun
    rw [freeProductHomEquiv_precomp_left] at hfun
    have hpoint := LocallyConstant.congr_fun hfun (PUnit.unit, s)
    rw [freeProductHomEquiv_zero_apply] at hpoint
    change ((numeratorHomEquiv S) q.1)
      ((TopCat.Hom.hom (ι ▷ S).hom) (PUnit.unit, s)) = 0
    simpa [numeratorHomEquiv] using hpoint
  invFun h := by
    refine ⟨(numeratorHomEquiv S).symm h.1, ?_⟩
    apply (freeProductHomEquiv (LightProfinite.of PUnit.{1}) S).injective
    ext x
    rcases x with ⟨u, s⟩
    cases u
    dsimp [P_map]
    rw [freeProductHomEquiv_precomp_left]
    rw [show (freeProductHomEquiv (ℕ∪{∞}) S) ((numeratorHomEquiv S).symm h.1) = h.1 by
      simp [numeratorHomEquiv]]
    change h.1 ((∞ : ℕ∪{∞}), s) =
      freeProductHomEquiv (LightProfinite.of PUnit.{1}) S
        (0 : (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⊗
          (free ℤ).obj S.toCondensed ⟶ Zdisc) (PUnit.unit, s)
    simp [h.2 s, freeProductHomEquiv_zero_apply]
  left_inv q := by
    ext
    simp
  right_inv h := by
    ext x
    simp [numeratorHomEquiv]

/-- Maps from `P ℤ ⊗ ℤ[S]` to `ℤ` as vanishing-at-infinity locally constant functions. -/
noncomputable def pTensorHomVanishEquiv (S : LightProfinite) :
    ((P ℤ ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) ≃ VanishAtInfinity S :=
  (pTensorHomSubtypeEquiv S).trans (numeratorSubtypeVanishEquiv S)

/-- Maps from `P ℤ ⊗ ℤ[S]` to `ℤ` as locally constant `S`-families of finitely supported
integer sequences. -/
noncomputable def nullSeqPointsEquiv (S : LightProfinite) :
    ((P ℤ ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) ≃ LocallyConstant S SeqZ :=
  (pTensorHomVanishEquiv S).trans (vanishAtInfinityEquiv S)

set_option backward.isDefEq.respectTransparency false in
lemma nullSeqPointsEquiv_apply (S : LightProfinite)
    (f : (P ℤ ⊗ (free ℤ).obj S.toCondensed) ⟶ Zdisc) (s : S) (n : ℕ) :
    nullSeqPointsEquiv S f s n =
      numeratorHomEquiv S ((pTensorHomSubtypeEquiv S f).1) ((n : ℕ∪{∞}), s) := by
  dsimp [nullSeqPointsEquiv, pTensorHomVanishEquiv, vanishAtInfinityEquiv]
  rw [vanishToSeq_apply]
  rfl

end PTensorHom

end LightCondensed.Solid.IntProof
