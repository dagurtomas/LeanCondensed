module

public import LeanCondensed.Projects.SolidProjectiveGenerator.PBasisTensorDesc
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- Sections of `ℤ` over `(ℕ∪∞) × T` are determined by all finite slices and the `∞` slice. -/
lemma zdisc_section_ext_of_slices (T : LightProfinite)
    (x y : Zdisc.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩)
    (hfinite : ∀ n : ℕ,
      Zdisc.obj.map (finiteTensorPoint T n).op x =
        Zdisc.obj.map (finiteTensorPoint T n).op y)
    (hinfty : Zdisc.obj.map (inftyTensorPoint T).op x =
      Zdisc.obj.map (inftyTensorPoint T).op y) :
    x = y := by
  apply (zdiscSectionsEquiv ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)).injective
  ext p
  rcases p with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      have h := congrArg (zdiscSectionsEquiv T) hinfty
      rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at h
      exact congrFun (congrArg LocallyConstant.toFun h) t
  | coe n =>
      have h := congrArg (zdiscSectionsEquiv T) (hfinite n)
      rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at h
      exact congrFun (congrArg LocallyConstant.toFun h) t

/-- Finite signed integer measures on a light profinite set. -/
abbrev FreeMeasure (T : LightProfinite) := T →₀ ℤ

lemma totalVariation_single_one_le_two {α : Type*} (a : α) :
    LightProfinite.FreeImage.totalVariation (Finsupp.single a (1 : ℤ)) ≤ (2 : ℤ) := by
  rw [LightProfinite.FreeImage.totalVariation]
  simp

lemma totalVariation_single_sub_single_le_two {α : Type*} [DecidableEq α] (a b : α) :
    LightProfinite.FreeImage.totalVariation
      (Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)) ≤ (2 : ℤ) := by
  classical
  let μ : α →₀ ℤ := Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ)
  have hsupp : μ.support ⊆ ({a, b} : Finset α) := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    have hxzero : μ x = 0 := by simp [μ, h.1, h.2]
    exact hx hxzero
  calc
    LightProfinite.FreeImage.totalVariation μ
        = ∑ x ∈ μ.support, |μ x| := by
          rw [LightProfinite.FreeImage.totalVariation, Finsupp.sum]
    _ ≤ ∑ x ∈ ({a, b} : Finset α), |μ x| := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsupp
            (by intro x _ _; positivity)
    _ ≤ 2 := by
          by_cases h : a = b
          · subst h
            simp [μ]
          · simp [μ, h, abs_of_nonneg, abs_of_nonpos]

/-- The finite signed measure underlying the tail family over `(ℕ∪∞) × T`. -/
noncomputable def topologicalTailMeasure (T : LightProfinite) :
    ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) → LightCondAb.topologicalFree T
  | (∞, _) => 0
  | (OnePoint.some 0, t) => Finsupp.single t (1 : ℤ)
  | (OnePoint.some (m + 1), t) =>
      Finsupp.single t (1 : ℤ) -
        Finsupp.single (LightProfinite.finiteApproxRetraction T m t) (1 : ℤ)

@[simp]
lemma topologicalTailMeasure_zero (T : LightProfinite) (t : T) :
    topologicalTailMeasure T (((0 : ℕ) : ℕ∪{∞}), t) = Finsupp.single t (1 : ℤ) := rfl

@[simp]
lemma topologicalTailMeasure_succ (T : LightProfinite) (m : ℕ) (t : T) :
    topologicalTailMeasure T (((m + 1 : ℕ) : ℕ∪{∞}), t) =
      Finsupp.single t (1 : ℤ) -
        Finsupp.single (LightProfinite.finiteApproxRetraction T m t) (1 : ℤ) := rfl

@[simp]
lemma topologicalTailMeasure_infty (T : LightProfinite) (t : T) :
    topologicalTailMeasure T ((∞ : ℕ∪{∞}), t) = 0 := rfl

lemma topologicalTailMeasure_totalVariation_le_two (T : LightProfinite)
    (x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)) :
    LightProfinite.FreeImage.totalVariation (topologicalTailMeasure T x) ≤ (2 : ℤ) := by
  classical
  rcases x with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      change LightProfinite.FreeImage.totalVariation (0 : T →₀ ℤ) ≤ (2 : ℤ)
      simp [LightProfinite.FreeImage.totalVariation]
  | coe n =>
      cases n with
      | zero => simpa [topologicalTailMeasure] using totalVariation_single_one_le_two t
      | succ m =>
          simpa [topologicalTailMeasure] using
            totalVariation_single_sub_single_le_two t
              (LightProfinite.finiteApproxRetraction T m t)

set_option backward.isDefEq.respectTransparency false in
/-- Continuity of every finite quotient projection of the topological tail family. -/
lemma topologicalTailMeasure_finiteProj_continuous (T : LightProfinite) (k : ℕ) :
    Continuous fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) =>
      (LightCondAb.topologicalFreeMap (T.proj k)).hom (topologicalTailMeasure T x) := by
  let f : ℕ → C(↑T.toTop, ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat) :=
    fun n => match n with
    | 0 => ⟨fun t =>
        (show ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat from
          Finsupp.single (T.proj k t) (1 : ℤ)),
        (LightCondAb.topologicalFreeDirac (T.component k)).hom.continuous.comp
          (T.proj k).hom.hom.continuous⟩
    | m + 1 => ⟨fun t =>
        (show ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat from
          Finsupp.single (T.proj k t) (1 : ℤ)) -
          (show ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat from
            Finsupp.single (T.proj k (LightProfinite.finiteApproxRetraction T m t)) (1 : ℤ)),
        by fun_prop⟩
  have hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0 := by
    refine Filter.eventually_atTop.2 ⟨k + 1, ?_⟩
    intro n hn
    ext t
    cases n with
    | zero => omega
    | succ m =>
        have hle : k ≤ m := by omega
        change (Finsupp.single (T.proj k t) (1 : ℤ) -
          Finsupp.single (T.proj k (LightProfinite.finiteApproxRetraction T m t)) 1 :
            T.component k →₀ ℤ) = 0
        have hpts : T.proj k (LightProfinite.finiteApproxRetraction T m t) = T.proj k t := by
          have hmap := congrArg (fun f : T ⟶ T.component k => f t)
            (LightProfinite.finiteApproxRetraction_proj_le T hle)
          simpa using hmap
        rw [hpts]
        simp
  have hcont := continuous_ninfTensor_of_eventually_eq_zero T f hf
  convert hcont using 1
  ext x
  rcases x with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty => exact (LightCondAb.topologicalFreeMap (T.proj k)).hom.map_zero
  | coe n =>
      cases n with
      | zero => simp [f, topologicalTailMeasure, LightCondAb.topologicalFreeMap_single]
      | succ m =>
          let μ₁ : LightCondAb.topologicalFree T := Finsupp.single t (1 : ℤ)
          let μ₂ : LightCondAb.topologicalFree T :=
            Finsupp.single (LightProfinite.finiteApproxRetraction T m t) (1 : ℤ)
          change (LightCondAb.topologicalFreeMap (T.proj k)).hom (μ₁ - μ₂) =
            (show ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat from
              Finsupp.single (T.proj k t) (1 : ℤ)) -
            (show ↑(LightCondAb.topologicalFree (T.component k)).toModuleCat from
              Finsupp.single (T.proj k (LightProfinite.finiteApproxRetraction T m t)) (1 : ℤ))
          rw [((LightCondAb.topologicalFreeMap (T.proj k)).hom).map_sub]
          dsimp [μ₁, μ₂]
          rw [LightCondAb.topologicalFreeMap_single]
          rw [LightCondAb.topologicalFreeMap_single]

lemma freeFiniteApproxRetraction_topologicalFree_apply
    (T : LightProfinite) (m : ℕ) (t : T) :
    (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)
          (freeFiniteApproxRetraction T m))) t =
      Finsupp.single (LightProfinite.finiteApproxRetraction T m t) (1 : ℤ) := by
  dsimp [freeFiniteApproxRetraction]
  exact freeMap_topologicalFree_apply (LightProfinite.finiteApproxRetraction T m) t

lemma freeTailEndomorphism_topologicalFree_apply
    (T : LightProfinite) (n : ℕ) (t : T) :
    (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed) (freeTailEndomorphism T n))) t =
      topologicalTailMeasure T ((n : ℕ∪{∞}), t) := by
  cases n with
  | zero =>
      exact freeToTopologicalFree_id_apply T t
  | succ m =>
      dsimp [freeTailEndomorphism]
      rw [freeHomEquivPoints_sub]
      let a := freeHomEquivPoints T ((free ℤ).obj T.toCondensed) (𝟙 ((free ℤ).obj T.toCondensed))
      let b := freeHomEquivPoints T ((free ℤ).obj T.toCondensed) (freeFiniteApproxRetraction T m)
      have hmap : (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ (a - b) =
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ a -
            (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ b := by
        exact ((LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩).hom.map_sub a b
      change (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ (a - b)) t = _
      rw [hmap]
      change (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ a) t -
        (show C(↑T.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨T⟩ b) t = _
      rw [freeToTopologicalFree_id_apply, freeFiniteApproxRetraction_topologicalFree_apply]
      rfl

/-- The signed difference of two Dirac measures in a represented topological-free group. -/
def topologicalFreeDiracDiff (T : LightProfinite) (a b : T) : LightCondAb.topologicalFree T :=
  (show ↑(LightCondAb.topologicalFree T).toModuleCat from
    Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ))

lemma topologicalFreeEval_diracDiff (T : LightProfinite) (f : LocallyConstant T ℤ) (a b : T) :
    (LightCondAb.topologicalFreeEval T f).hom (topologicalFreeDiracDiff T a b) = f a - f b := by
  let μ₁ : LightCondAb.topologicalFree T := Finsupp.single a (1 : ℤ)
  let μ₂ : LightCondAb.topologicalFree T := Finsupp.single b (1 : ℤ)
  change (LightCondAb.topologicalFreeEval T f).hom (μ₁ - μ₂) = f a - f b
  rw [map_sub]
  dsimp [μ₁, μ₂]
  rw [LightCondAb.topologicalFreeEval_single]
  rw [LightCondAb.topologicalFreeEval_single]

lemma topologicalFreeMap_diracDiff {T U : LightProfinite} (q : T ⟶ U) (a b : T) :
    (LightCondAb.topologicalFreeMap q).hom (topologicalFreeDiracDiff T a b) =
      topologicalFreeDiracDiff U (q a) (q b) := by
  let μ₁ : LightCondAb.topologicalFree T := Finsupp.single a (1 : ℤ)
  let μ₂ : LightCondAb.topologicalFree T := Finsupp.single b (1 : ℤ)
  change (LightCondAb.topologicalFreeMap q).hom (μ₁ - μ₂) =
    (show ↑(LightCondAb.topologicalFree U).toModuleCat from
      Finsupp.single (q a) (1 : ℤ) - Finsupp.single (q b) (1 : ℤ))
  rw [((LightCondAb.topologicalFreeMap q).hom).map_sub]
  dsimp [μ₁, μ₂]
  rw [LightCondAb.topologicalFreeMap_single]
  rw [LightCondAb.topologicalFreeMap_single]
  rfl

lemma topologicalFreeDiracDiff_self (T : LightProfinite) (a : T) :
    topologicalFreeDiracDiff T a a = 0 := by
  simp [topologicalFreeDiracDiff]
  rfl

lemma totalVariation_zsmul_diracDiff_le_two_mul_natAbs {α : Type*} [DecidableEq α]
    (a b : α) (c : ℤ) :
    LightProfinite.FreeImage.totalVariation
      (c • (Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ))) ≤
        (2 * (Int.natAbs c : ℤ)) := by
  classical
  let μ : α →₀ ℤ := c • (Finsupp.single a (1 : ℤ) - Finsupp.single b (1 : ℤ))
  have hsupp : μ.support ⊆ ({a, b} : Finset α) := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    have hxzero : μ x = 0 := by simp [μ, h.1, h.2]
    exact hx hxzero
  calc
    LightProfinite.FreeImage.totalVariation μ
        = ∑ x ∈ μ.support, |μ x| := by
          rw [LightProfinite.FreeImage.totalVariation, Finsupp.sum]
    _ ≤ ∑ x ∈ ({a, b} : Finset α), |μ x| := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsupp
            (by intro x _ _; positivity)
    _ ≤ 2 * (Int.natAbs c : ℤ) := by
          by_cases h : a = b
          · subst h
            simp [μ]
          · simp [μ, h, abs_of_nonneg, abs_of_nonpos]
            ring_nf
            exact le_rfl

lemma ninf_map_eventually_eq_infty (F : LightProfinite) [Finite F]
    (q : (ℕ∪{∞} : LightProfinite) ⟶ F) :
    ∀ᶠ n : ℕ in Filter.atTop, q (n : ℕ∪{∞}) = q (∞ : ℕ∪{∞}) := by
  letI : DiscreteTopology F := Finite.instDiscreteTopology
  have hcont : Continuous (fun a : (ℕ∪{∞} : LightProfinite) => q a) := q.hom.hom.continuous
  have htend : Filter.Tendsto (fun n : ℕ => q (n : ℕ∪{∞})) Filter.atTop
      (nhds (q (∞ : ℕ∪{∞}))) :=
    (LightProfinite.continuous_iff_convergent
      (fun a : (ℕ∪{∞} : LightProfinite) => q a)).mp hcont
  have hsing : {q (∞ : ℕ∪{∞})} ∈ nhds (q (∞ : ℕ∪{∞})) := by
    simp [nhds_discrete]
  filter_upwards [htend hsing] with n hn
  simpa using hn

/-- The coefficient of the bounded diagonal-difference measure.  It is zero at `∞` and is the
corresponding bounded-sequence coordinate at finite points. -/
def boundedDifferenceCoeff {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) (s : S) : ℤ :=
  match f s with
  | ∞ => 0
  | OnePoint.some n => x.val n s

/-- The pointwise signed measure `m_{f(s)}(s) • (δ_{f(s)} - δ_∞)`. -/
def boundedDifferenceMeasure {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) (s : S) :
    LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite) :=
  boundedDifferenceCoeff f x s •
    topologicalFreeDiracDiff (ℕ∪{∞} : LightProfinite) (f s) (∞ : ℕ∪{∞})

lemma boundedDifferenceMeasure_add {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x y : BoundedIntSeqSection S) (s : S) :
    boundedDifferenceMeasure f (x + y) s =
      boundedDifferenceMeasure f x s + boundedDifferenceMeasure f y s := by
  dsimp [boundedDifferenceMeasure]
  cases hfs : f s using OnePoint.rec with
  | infty => simp [boundedDifferenceCoeff, hfs]
  | coe n =>
      have hxy : boundedDifferenceCoeff f (x + y) s = x.val n s + y.val n s := by
        simp [boundedDifferenceCoeff, hfs]
      have hx : boundedDifferenceCoeff f x s = x.val n s := by
        simp [boundedDifferenceCoeff, hfs]
      have hy : boundedDifferenceCoeff f y s = y.val n s := by
        simp [boundedDifferenceCoeff, hfs]
      rw [hxy, hx, hy]
      let d := topologicalFreeDiracDiff (ℕ∪{∞} : LightProfinite)
        (n : ℕ∪{∞}) (∞ : ℕ∪{∞})
      change ((x.val n s + y.val n s) • d) = (x.val n s) • d + (y.val n s) • d
      rw [add_zsmul]

lemma boundedDifferenceMeasure_zsmul {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (a : ℤ) (x : BoundedIntSeqSection S) (s : S) :
    boundedDifferenceMeasure f (a • x) s = a • boundedDifferenceMeasure f x s := by
  dsimp [boundedDifferenceMeasure]
  cases hfs : f s using OnePoint.rec with
  | infty =>
      dsimp [boundedDifferenceCoeff]
      rw [hfs]
      rw [topologicalFreeDiracDiff_self]
      simp
      exact (smul_zero a : a • (0 : LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)) = 0).symm
  | coe n =>
      have hax : boundedDifferenceCoeff f (a • x) s = a * x.val n s := by
        dsimp [boundedDifferenceCoeff]
        rw [hfs]
      have hx : boundedDifferenceCoeff f x s = x.val n s := by
        simp [boundedDifferenceCoeff, hfs]
      rw [hax, hx]
      let d := topologicalFreeDiracDiff (ℕ∪{∞} : LightProfinite)
        (n : ℕ∪{∞}) (∞ : ℕ∪{∞})
      change (a * x.val n s) • d = a • ((x.val n s) • d)
      rw [mul_smul]

lemma boundedDifferenceMeasure_comap {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S)
    (t : T) :
    boundedDifferenceMeasure (g ≫ f) (boundedIntSeqSectionComap g x) t =
      boundedDifferenceMeasure f x (g t) := by
  dsimp [boundedDifferenceMeasure, boundedDifferenceCoeff]
  rfl

lemma boundedDifferenceMeasure_totalVariation_le {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) (s : S) :
    LightProfinite.FreeImage.totalVariation (boundedDifferenceMeasure f x s) ≤
      (2 * x.isBounded.choose : ℤ) := by
  classical
  dsimp [boundedDifferenceMeasure, topologicalFreeDiracDiff]
  have hcoeff : Int.natAbs (boundedDifferenceCoeff f x s) ≤ x.isBounded.choose := by
    cases hfs : f s using OnePoint.rec with
    | infty => simp [boundedDifferenceCoeff, hfs]
    | coe n =>
        simpa [boundedDifferenceCoeff, hfs] using x.isBounded.choose_spec s n
  have htv := totalVariation_zsmul_diracDiff_le_two_mul_natAbs (f s)
    (∞ : ℕ∪{∞}) (boundedDifferenceCoeff f x s)
  refine le_trans htv ?_
  exact_mod_cast Nat.mul_le_mul_left 2 hcoeff

set_option backward.isDefEq.respectTransparency false in
lemma boundedDifferenceMeasure_finiteProj_continuous {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) (k : ℕ) :
    Continuous fun s : S =>
      (LightCondAb.topologicalFreeMap ((ℕ∪{∞} : LightProfinite).proj k)).hom
        (boundedDifferenceMeasure f x s) := by
  let q : (ℕ∪{∞} : LightProfinite) ⟶ (ℕ∪{∞} : LightProfinite).component k :=
    (ℕ∪{∞} : LightProfinite).proj k
  let g : ℕ → C(↑S.toTop,
      ↑(LightCondAb.topologicalFree ((ℕ∪{∞} : LightProfinite).component k)).toModuleCat) := fun n =>
    ⟨fun s => (x.val n s) •
        topologicalFreeDiracDiff ((ℕ∪{∞} : LightProfinite).component k)
          (q (n : ℕ∪{∞})) (q (∞ : ℕ∪{∞})),
      by exact ((x.val n).map (fun z : ℤ ↦ z •
        topologicalFreeDiracDiff ((ℕ∪{∞} : LightProfinite).component k)
          (q (n : ℕ∪{∞})) (q (∞ : ℕ∪{∞})))).continuous⟩
  have hg : ∀ᶠ n : ℕ in Filter.atTop, g n = 0 := by
    filter_upwards [ninf_map_eventually_eq_infty ((ℕ∪{∞} : LightProfinite).component k) q] with n hn
    ext s
    change (x.val n s) •
        topologicalFreeDiracDiff ((ℕ∪{∞} : LightProfinite).component k)
          (q (n : ℕ∪{∞})) (q (∞ : ℕ∪{∞})) = 0
    rw [hn]
    rw [topologicalFreeDiracDiff_self]
    exact smul_zero (x.val n s)
  have hcont := continuous_ninfTensor_of_eventually_eq_zero S g hg
  have hgraph : Continuous fun s : S => ((f s), s) := by
    exact f.hom.hom.continuous.prodMk continuous_id
  refine (hcont.comp hgraph).congr ?_
  intro s
  dsimp [boundedDifferenceMeasure, Function.comp_def]
  cases hfs : f s using OnePoint.rec with
  | infty =>
      simp [boundedDifferenceCoeff, hfs]
      exact (LightCondAb.topologicalFreeMap q).hom.map_zero.symm
  | coe n =>
      have hcoeff : boundedDifferenceCoeff f x s = x.val n s := by
        simp [boundedDifferenceCoeff, hfs]
      rw [hcoeff]
      change (x.val n s) •
          topologicalFreeDiracDiff ((ℕ∪{∞} : LightProfinite).component k)
            (q (n : ℕ∪{∞})) (q (∞ : ℕ∪{∞})) =
        (LightCondAb.topologicalFreeMap q).hom
          ((x.val n s) • topologicalFreeDiracDiff (ℕ∪{∞} : LightProfinite)
            (n : ℕ∪{∞}) (∞ : ℕ∪{∞}))
      rw [map_smul]
      rw [topologicalFreeMap_diracDiff]

/-- The represented topological-free section underlying the bounded diagonal-difference family. -/
noncomputable def boundedDifferenceTopologicalSection {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    (LightCondAb.topologicalFreeCondensed (ℕ∪{∞} : LightProfinite)).obj.obj ⟨S⟩ :=
  LightCondAb.topologicalFreeSectionOfBoundedFiniteProj (ℕ∪{∞} : LightProfinite) S
    (boundedDifferenceMeasure f x) (2 * x.isBounded.choose)
    (boundedDifferenceMeasure_totalVariation_le f x)
    (boundedDifferenceMeasure_finiteProj_continuous f x)

lemma boundedDifferenceTopologicalSection_add {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x y : BoundedIntSeqSection S) :
    boundedDifferenceTopologicalSection f (x + y) =
      boundedDifferenceTopologicalSection f x + boundedDifferenceTopologicalSection f y := by
  apply ContinuousMap.ext
  intro s
  change boundedDifferenceMeasure f (x + y) s =
    boundedDifferenceMeasure f x s + boundedDifferenceMeasure f y s
  exact boundedDifferenceMeasure_add f x y s

lemma boundedDifferenceTopologicalSection_zsmul {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (a : ℤ) (x : BoundedIntSeqSection S) :
    boundedDifferenceTopologicalSection f (a • x) =
      a • boundedDifferenceTopologicalSection f x := by
  apply ContinuousMap.ext
  intro s
  change boundedDifferenceMeasure f (a • x) s = a • boundedDifferenceMeasure f x s
  exact boundedDifferenceMeasure_zsmul f a x s

lemma boundedDifferenceTopologicalSection_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    (LightCondAb.topologicalFreeCondensed (ℕ∪{∞} : LightProfinite)).obj.map g.op
      (boundedDifferenceTopologicalSection f x) =
    boundedDifferenceTopologicalSection (g ≫ f) (boundedIntSeqSectionComap g x) := by
  apply ContinuousMap.ext
  intro t
  change boundedDifferenceMeasure f x (g t) =
    boundedDifferenceMeasure (g ≫ f) (boundedIntSeqSectionComap g x) t
  exact (boundedDifferenceMeasure_comap g f x t).symm

/-- The `P`-valued section obtained by projecting the bounded diagonal-difference free section. -/
noncomputable def boundedDifferencePSection {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    (P ℤ).obj.obj ⟨S⟩ :=
  (P_proj ℤ).hom.app ⟨S⟩
    ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).symm.hom.hom.app ⟨S⟩
      (boundedDifferenceTopologicalSection f x))

lemma boundedDifferencePSection_add {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x y : BoundedIntSeqSection S) :
    boundedDifferencePSection f (x + y) =
      boundedDifferencePSection f x + boundedDifferencePSection f y := by
  dsimp [boundedDifferencePSection]
  rw [boundedDifferenceTopologicalSection_add]
  rw [((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom.map_add]
  rw [((P_proj ℤ).hom.app ⟨S⟩).hom.map_add]

lemma boundedDifferencePSection_zsmul {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (a : ℤ) (x : BoundedIntSeqSection S) :
    boundedDifferencePSection f (a • x) = a • boundedDifferencePSection f x := by
  dsimp [boundedDifferencePSection]
  rw [boundedDifferenceTopologicalSection_zsmul]
  let u := boundedDifferenceTopologicalSection f x
  have hfree :
      ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom
        (a • u) =
      a • ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom u := by
    exact map_zsmul
      (((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom) a u
  change ((P_proj ℤ).hom.app ⟨S⟩).hom
      (((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom
        (a • u)) =
    a • ((P_proj ℤ).hom.app ⟨S⟩).hom
      (((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom u)
  rw [hfree]
  exact map_zsmul (((P_proj ℤ).hom.app ⟨S⟩).hom) a _

lemma boundedDifferencePSection_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    (P ℤ).obj.map g.op (boundedDifferencePSection f x) =
      boundedDifferencePSection (g ≫ f) (boundedIntSeqSectionComap g x) := by
  dsimp [boundedDifferencePSection]
  rw [← LightCondMod.hom_naturality_apply ℤ (P_proj ℤ) g.op]
  rw [← LightCondMod.hom_naturality_apply ℤ
    (LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv g.op]
  rw [boundedDifferenceTopologicalSection_naturality]

/-- The sectionwise linear family defining the bounded diagonal-difference numerator. -/
noncomputable def boundedDifferenceFamilyLinear (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) :
    boundedIntSequences.obj.obj ⟨S⟩ →ₗ[ℤ] (P ℤ).obj.obj ⟨S⟩ where
  toFun x := boundedDifferencePSection f (show BoundedIntSeqSection S from x)
  map_add' := by
    intro x y
    exact boundedDifferencePSection_add f (show BoundedIntSeqSection S from x)
      (show BoundedIntSeqSection S from y)
  map_smul' := by
    intro a x
    have hx : (show BoundedIntSeqSection S from a • x) =
        a • (show BoundedIntSeqSection S from x) := by
      apply BoundedIntSeqSection.ext_apply
      intro n s
      rfl
    convert boundedDifferencePSection_zsmul f a (show BoundedIntSeqSection S from x) using 1
    · exact congrArg (boundedDifferencePSection f) hx
    · simpa [RingHom.id_apply] using
        (Int.cast_smul_eq_zsmul (R := ℤ) a
          (boundedDifferencePSection f (show BoundedIntSeqSection S from x)))

lemma boundedDifferenceFamilyLinear_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : boundedIntSequences.obj.obj ⟨S⟩) :
    (P ℤ).obj.map g.op (boundedDifferenceFamilyLinear S f m) =
      boundedDifferenceFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  exact boundedDifferencePSection_naturality g f (show BoundedIntSeqSection S from m)

lemma boundedDifferenceFamilyLinear_naturality' :
    ∀ {S T : LightProfinite} (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
      (m : boundedIntSequences.obj.obj ⟨S⟩),
      (P ℤ).obj.map g.op (boundedDifferenceFamilyLinear S f m) =
        boundedDifferenceFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  intro S T g f m
  exact boundedDifferenceFamilyLinear_naturality g f m

/-- The free numerator for the bounded diagonal-difference map. -/
noncomputable def boundedDifferenceNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ boundedIntSequences ⟶ P ℤ :=
  freeTensorDescLin (ℕ∪{∞} : LightProfinite) boundedIntSequences (P ℤ)
    boundedDifferenceFamilyLinear boundedDifferenceFamilyLinear_naturality'

/-- Finite slices of the bounded diagonal-difference numerator are given by the defining family. -/
lemma boundedDifferenceNumerator_slice (n : ℕ) :
    numeratorSlice boundedIntSequences (P ℤ) n boundedDifferenceNumerator =
      freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences (P ℤ)
        boundedDifferenceFamilyLinear boundedDifferenceFamilyLinear_naturality' (natPoint n) := by
  dsimp [numeratorSlice, freeNatBasis, boundedDifferenceNumerator]
  rw [freeTensorDescLin_point]

set_option backward.isDefEq.respectTransparency false in
lemma boundedDifferenceFamilyMap_infty :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences (P ℤ)
      boundedDifferenceFamilyLinear boundedDifferenceFamilyLinear_naturality' ι =
    0 := by
  ext S x
  change boundedDifferenceFamilyLinear S.unop (toPointMap S.unop ≫ ι) x =
    (0 : boundedIntSequences ⟶ P ℤ).hom.app S x
  dsimp [boundedDifferenceFamilyLinear, boundedDifferencePSection]
  have htop : boundedDifferenceTopologicalSection (toPointMap S.unop ≫ ι)
      (show BoundedIntSeqSection S.unop from x) = 0 := by
    apply ContinuousMap.ext
    intro s
    change boundedDifferenceMeasure (toPointMap S.unop ≫ ι)
        (show BoundedIntSeqSection S.unop from x) s = 0
    dsimp [boundedDifferenceMeasure, boundedDifferenceCoeff]
    have hf : (ConcreteCategory.hom (toPointMap S.unop ≫ ι)) s =
        (∞ : ℕ∪{∞}) := rfl
    rw [hf]
    rw [topologicalFreeDiracDiff_self]
    change (0 : ℤ) • (0 : LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)) = 0
    exact zero_smul ℤ (0 : LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite))
  rw [htop]
  simp

/-- The bounded diagonal-difference numerator has zero `∞` slice. -/
lemma boundedDifferenceNumerator_infty :
    inftySlice boundedIntSequences (P ℤ) boundedDifferenceNumerator = 0 := by
  dsimp [inftySlice, freeInftyBasis, P_map, boundedDifferenceNumerator]
  rw [freeTensorDescLin_point]
  exact boundedDifferenceFamilyMap_infty

/-- The bounded diagonal-difference numerator kills the basepoint summand. -/
lemma boundedDifferenceNumerator_kills :
    (P_map ℤ ▷ boundedIntSequences) ≫ boundedDifferenceNumerator = 0 :=
  numerator_kills_of_inftySlice_zero boundedIntSequences (P ℤ)
    boundedDifferenceNumerator boundedDifferenceNumerator_infty

/-- The bounded diagonal-difference map descended to `P ℤ ⊗ boundedIntSequences`. -/
noncomputable def boundedDifferenceMap :
    P ℤ ⊗ boundedIntSequences ⟶ P ℤ :=
  pTensorDesc boundedIntSequences (P ℤ) boundedDifferenceNumerator
    boundedDifferenceNumerator_kills

/-- Finite slices of the descended bounded diagonal-difference map. -/
lemma boundedDifferenceMap_slice (n : ℕ) :
    ((λ_ boundedIntSequences).inv ≫ pBasis n ▷ boundedIntSequences) ≫ boundedDifferenceMap =
      freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences (P ℤ)
        boundedDifferenceFamilyLinear boundedDifferenceFamilyLinear_naturality' (natPoint n) := by
  dsimp [boundedDifferenceMap]
  rw [pTensorDesc_slice]
  exact boundedDifferenceNumerator_slice n

lemma boundedDifferenceFamilyMap_natPoint_comp_basisMap (n : ℕ) :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences (P ℤ)
      boundedDifferenceFamilyLinear boundedDifferenceFamilyLinear_naturality' (natPoint n) ≫ basisMap =
      boundedTailProjection n - boundedTailProjection (n + 1) := by
  ext S x
  apply BoundedIntSeqSection.ext_apply
  intro k s
  let fconst : S.unop ⟶ (ℕ∪{∞} : LightProfinite) := toPointMap S.unop ≫ natPoint n
  let topSec : (LightCondAb.topologicalFreeCondensed (ℕ∪{∞} : LightProfinite)).obj.obj S :=
    boundedDifferenceTopologicalSection fconst (show BoundedIntSeqSection S.unop from x)
  let freeSec : ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.obj S :=
    (LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).symm.hom.hom.app S topSec
  have hcoord := boundedCoord_apply S.unop
    ((basisMap.hom.app S) (boundedDifferenceFamilyLinear S.unop fconst x)) k
  change zdiscSectionsEquiv S.unop
      (((boundedCoord k).hom.app S)
        ((basisMap.hom.app S) (boundedDifferenceFamilyLinear S.unop fconst x))) =
    (boundedIntSequencesSectionsEquiv S.unop
      ((basisMap.hom.app S) (boundedDifferenceFamilyLinear S.unop fconst x))).val k at hcoord
  have hleft : zdiscSectionsEquiv S.unop
      (((boundedCoord k).hom.app S)
        ((basisMap.hom.app S) (boundedDifferenceFamilyLinear S.unop fconst x))) s =
      (boundedStandardBasisCoord k (n : ℕ∪{∞})) *
        (show BoundedIntSeqSection S.unop from x).val n s := by
    dsimp [boundedDifferenceFamilyLinear, boundedDifferencePSection, fconst, freeSec, topSec]
    change zdiscSectionsEquiv S.unop
        (((P_proj ℤ ≫ basisMap ≫ boundedCoord k).hom.app S) freeSec) s = _
    rw [P_proj_comp_basisMap_boundedCoord]
    rw [zdiscMapOfLocallyConstant_eq_freeToTopologicalFree_eval]
    change zdiscSectionsEquiv S.unop
        ((LightCondAb.topologicalFreeEvalDiscrete (ℕ∪{∞} : LightProfinite)
            (boundedStandardBasisCoord k)).hom.app S
          ((LightCondAb.freeToTopologicalFree (ℕ∪{∞} : LightProfinite)).hom.app S freeSec)) s = _
    rw [LightCondAb.freeToTopologicalFree_app_section_of_iso_symm]
    rw [zdiscSectionsEquiv_topologicalFreeEvalDiscrete_apply]
    dsimp [topSec, boundedDifferenceTopologicalSection]
    change (LightCondAb.topologicalFreeEval (ℕ∪{∞} : LightProfinite)
        (boundedStandardBasisCoord k)).hom
        (boundedDifferenceMeasure fconst (show BoundedIntSeqSection S.unop from x) s) = _
    dsimp [boundedDifferenceMeasure, boundedDifferenceCoeff]
    change (LightCondAb.topologicalFreeEval (ℕ∪{∞} : LightProfinite)
        (boundedStandardBasisCoord k)).hom
        (((show BoundedIntSeqSection S.unop from x).val n s) •
          topologicalFreeDiracDiff (ℕ∪{∞} : LightProfinite) (n : ℕ∪{∞}) (∞ : ℕ∪{∞})) = _
    rw [map_zsmul]
    rw [topologicalFreeEval_diracDiff]
    rw [boundedStandardBasisCoord_infty]
    ring
  have hcoord_point := congrArg (fun lc : LocallyConstant S.unop ℤ => lc s) hcoord
  rw [hleft] at hcoord_point
  change (((boundedIntSequencesSectionsEquiv S.unop
      ((basisMap.hom.app S) (boundedDifferenceFamilyLinear S.unop fconst x))).val k) s) =
    (((boundedIntSequencesSectionsEquiv S.unop
      (((boundedTailProjection n - boundedTailProjection (n + 1)).hom.app S) x)).val k) s)
  rw [← hcoord_point]
  rw [boundedTailProjection_succ_diff_apply_coord]
  rw [boundedStandardBasisCoord_finite]
  by_cases hkn : n = k
  · subst k
    simp
    change (x.val n) s = (x.val n) s
    rfl
  · have hkn' : k ≠ n := by exact fun hk => hkn hk.symm
    simp [hkn, hkn']

/-- The numerator-level bounded shift-retract square. -/
lemma boundedShiftRetract_numerator_comm :
    (oneMinusShift' ℤ ▷ boundedIntSequences) ≫ boundedTailNumerator =
      boundedDifferenceNumerator ≫ basisMap := by
  apply boundedTarget_numerator_ext_of_slices
  · intro n
    rw [numeratorSlice_oneMinusShift']
    rw [boundedTailNumerator_slice]
    rw [boundedTailNumerator_slice]
    rw [numeratorSlice_comp]
    rw [boundedDifferenceNumerator_slice]
    rw [boundedDifferenceFamilyMap_natPoint_comp_basisMap]
  · rw [inftySlice_oneMinusShift']
    rw [inftySlice_comp]
    rw [boundedDifferenceNumerator_infty]
    simp

/-- The bounded shift-retract square for Lemma 3.3.3. -/
lemma boundedShiftRetract_comm :
    ((oneMinusShift ℤ) ▷ boundedIntSequences) ≫ boundedTailMap =
      boundedDifferenceMap ≫ basisMap := by
  haveI : Epi (P_proj ℤ ▷ boundedIntSequences) := epi_P_proj_tensor boundedIntSequences
  apply (cancel_epi (P_proj ℤ ▷ boundedIntSequences)).1
  dsimp [boundedTailMap, boundedDifferenceMap]
  rw [← Category.assoc]
  rw [P_proj_tensor_oneMinusShift]
  rw [Category.assoc]
  rw [pTensorDesc_comp_proj]
  rw [← Category.assoc]
  rw [pTensorDesc_comp_proj]
  exact boundedShiftRetract_numerator_comm

end ProjectiveGeneratorProof
end Solid
end LightCondensed
