module

public import LeanCondensed.Projects.SolidProjectiveGenerator.SolidFreeRetracts
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The `Zdisc`-valued map out of `ℤ[T]` induced by a locally constant integer-valued
function on `T`. -/
noncomputable def zdiscMapOfLocallyConstant (T : LightProfinite)
    (f : LocallyConstant T ℤ) :
    (free ℤ).obj T.toCondensed ⟶ Zdisc :=
  (freeHomEquivPoints T Zdisc).symm ((zdiscSectionsEquiv T).symm f)

@[simp]
lemma freeHomEquivPoints_zdiscMapOfLocallyConstant (T : LightProfinite)
    (f : LocallyConstant T ℤ) :
    freeHomEquivPoints T Zdisc (zdiscMapOfLocallyConstant T f) =
      (zdiscSectionsEquiv T).symm f := by
  dsimp [zdiscMapOfLocallyConstant]
  rw [Equiv.apply_symm_apply]

@[simp]
lemma zdiscSectionsEquiv_zdiscMapOfLocallyConstant (T : LightProfinite)
    (f : LocallyConstant T ℤ) :
    zdiscSectionsEquiv T (freeHomEquivPoints T Zdisc (zdiscMapOfLocallyConstant T f)) = f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The `Zdisc` map induced by a locally constant function agrees with the represented-topological
free evaluation after the canonical comparison to the topological free abelian group. -/
lemma zdiscMapOfLocallyConstant_eq_freeToTopologicalFree_eval (T : LightProfinite)
    (f : LocallyConstant T ℤ) :
    zdiscMapOfLocallyConstant T f =
      LightCondAb.freeToTopologicalFree T ≫ LightCondAb.topologicalFreeEvalDiscrete T f := by
  apply (freeHomEquivPoints T Zdisc).injective
  apply (zdiscSectionsEquiv T).injective
  rw [freeHomEquivPoints_zdiscMapOfLocallyConstant]
  rw [freeHomEquivPoints_comp]
  have hfree : freeHomEquivPoints T (LightCondAb.topologicalFreeCondensed T)
      (LightCondAb.freeToTopologicalFree T) =
      (coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection T) := by
    simp [LightCondAb.freeToTopologicalFree, freeHomEquivPoints]
    rfl
  rw [hfree]
  simp only [Equiv.apply_symm_apply]
  change f = zdiscSectionsEquiv T
    ((LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨T⟩
      ((coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection T)))
  have hz : zdiscSectionsEquiv T
      ((LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨T⟩
        ((coherentTopology LightProfinite).yonedaEquiv (LightCondAb.topologicalFreeDiracSection T))) = f := by
    dsimp [zdiscSectionsEquiv]
    exact LightCondAb.topologicalFreeEvalDiscrete_diracSection T f
  rw [hz]

lemma zdiscSectionsEquiv_topologicalFreeEvalDiscrete_apply (T S : LightProfinite)
    (f : LocallyConstant T ℤ)
    (x : (LightCondAb.topologicalFreeCondensed T).obj.obj ⟨S⟩) (s : S) :
    zdiscSectionsEquiv S ((LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨S⟩ x) s =
      (LightCondAb.topologicalFreeEval T f).hom
        ((show C(↑S.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from x) s) := by
  rw [show LightCondAb.topologicalFreeEvalDiscrete T f =
    LightCondAb.topologicalFreeEvalCondensed T f ≫
      LightCondAb.discreteIntTopModuleCondensedIso.hom by rfl]
  change (show LocallyConstant S ℤ from
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      (LightCondAb.discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩
        ((LightCondAb.topologicalFreeEvalCondensed T f).hom.app ⟨S⟩ x))) s = _
  rw [LightCondAb.discreteIntTopModuleCondensedIso_sections]
  rfl

/-- Reconstruct a `Zdisc`-valued map from the locally constant function it induces. -/
lemma zdiscMapOfLocallyConstant_of_freeHomEquivPoints (T : LightProfinite)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    zdiscMapOfLocallyConstant T (zdiscSectionsEquiv T (freeHomEquivPoints T Zdisc φ)) = φ := by
  apply (freeHomEquivPoints T Zdisc).injective
  simp [zdiscMapOfLocallyConstant]

/-- A `ℤ`-valued map out of `ℤ[T]` factors through a finite quotient of `T`. -/
lemma zdisc_hom_factors_freeProj (T : LightProfinite)
    (φ : (free ℤ).obj T.toCondensed ⟶ Zdisc) :
    ∃ k : ℕ, ∃ ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc,
      freeProj T k ≫ ψ = φ := by
  let f : LocallyConstant T ℤ := zdiscSectionsEquiv T (freeHomEquivPoints T Zdisc φ)
  obtain ⟨k, g, hg⟩ := LightProfinite.exists_locallyConstant_factor_proj T f
  let ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc :=
    (freeHomEquivPoints (T.component k) Zdisc).symm
      ((zdiscSectionsEquiv (T.component k)).symm g)
  refine ⟨k, ψ, ?_⟩
  apply (freeHomEquivPoints T Zdisc).injective
  change freeHomEquivPoints T Zdisc
      (((free ℤ).map (lightProfiniteToLightCondSet.map (T.proj k))) ≫ ψ) =
    freeHomEquivPoints T Zdisc φ
  rw [freeHomEquivPoints_map]
  apply (zdiscSectionsEquiv T).injective
  rw [zdiscSectionsEquiv_map]
  dsimp [ψ, f] at hg ⊢
  rw [hg]
  simp

/-- Maps from a free object to the discrete integers are determined by their values on ordinary
points. -/
lemma zdisc_hom_ext_of_points (T : LightProfinite)
    (f g : (free ℤ).obj T.toCondensed ⟶ Zdisc)
    (h : ∀ t : T, freePointMap T t ≫ f = freePointMap T t ≫ g) :
    f = g := by
  apply (freeHomEquivPoints T Zdisc).injective
  apply (zdiscSectionsEquiv T).injective
  ext t
  let pt : LightProfinite := LightProfinite.of PUnit.{1}
  have hp := congrArg (freeHomEquivPoints pt Zdisc) (h t)
  dsimp [freePointMap] at hp
  rw [freeHomEquivPoints_map, freeHomEquivPoints_map] at hp
  have hz := congrArg (zdiscSectionsEquiv pt) hp
  rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map] at hz
  exact congrFun (congrArg LocallyConstant.toFun hz) PUnit.unit

/-- The free-module endomorphism induced by the finite-rank retraction of an infinite test object. -/
noncomputable def freeFiniteApproxRetraction (T : LightProfinite) (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (LightProfinite.finiteApproxRetraction T n)

/-- The finite-rank free-module retraction agrees with the identity after projection to any earlier
finite stage. -/
lemma freeFiniteApproxRetraction_freeProj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    freeFiniteApproxRetraction T n ≫ freeProj T k = freeProj T k := by
  dsimp [freeFiniteApproxRetraction, freeProj]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [LightProfinite.finiteApproxRetraction_proj_le T h]

/-- The tail endomorphisms used in Lemma 3.3.2: the zeroth term is the identity, and the successor
terms are `id -` the finite-rank approximations. -/
noncomputable def freeTailEndomorphism (T : LightProfinite) : ℕ →
    ((free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed)
  | 0 => 𝟙 _
  | n + 1 => 𝟙 _ - freeFiniteApproxRetraction T n

/-- Every fixed finite projection kills all sufficiently far tail endomorphisms. -/
lemma freeTailEndomorphism_succ_freeProj_zero (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    freeTailEndomorphism T (n + 1) ≫ freeProj T k = 0 := by
  dsimp [freeTailEndomorphism]
  rw [Preadditive.sub_comp]
  rw [Category.id_comp]
  rw [freeFiniteApproxRetraction_freeProj_le T h]
  abel

/-- Along every fixed finite quotient of `T`, the tail endomorphisms are eventually zero. -/
lemma freeTailEndomorphism_eventually_freeProj_zero (T : LightProfinite) (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, freeTailEndomorphism T n ≫ freeProj T k = 0 := by
  refine Filter.eventually_atTop.2 ⟨k + 1, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ n =>
      apply freeTailEndomorphism_succ_freeProj_zero T
      omega

/-- The map from the point to `ℕ∪∞` selecting the natural number `n`. -/
noncomputable def natPoint (n : ℕ) : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => (n : ℕ∪{∞}), continuous_const⟩

@[simp]
lemma natPoint_comp_shift (n : ℕ) :
    natPoint n ≫ LightProfinite.shift = natPoint (n + 1) := by
  ext x
  rfl

/-- The slice map `T → (ℕ∪∞) × T` selecting the finite index `n`. -/
noncomputable def finiteTensorPoint (T : LightProfinite) (n : ℕ) :
    T ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  (λ_ T).inv ≫ natPoint n ▷ T

/-- The slice map `T → (ℕ∪∞) × T` selecting the point `∞`. -/
noncomputable def inftyTensorPoint (T : LightProfinite) :
    T ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  (λ_ T).inv ≫ ι ▷ T

@[simp]
lemma finiteTensorPoint_apply (T : LightProfinite) (n : ℕ) (t : T) :
    finiteTensorPoint T n t = ((n : ℕ∪{∞}), t) := rfl

@[simp]
lemma inftyTensorPoint_apply (T : LightProfinite) (t : T) :
    inftyTensorPoint T t = ((∞ : ℕ∪{∞}), t) := rfl

/-- The section `ℕ∪∞ → (ℕ∪∞) × T` choosing a fixed point of `T`. -/
noncomputable def ninfPointSection (T : LightProfinite) (t : T) :
    (ℕ∪{∞} : LightProfinite) ⟶ ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) :=
  ConcreteCategory.ofHom ⟨fun a => (a, t), continuous_id.prodMk continuous_const⟩

@[simp]
lemma natPoint_comp_ninfPointSection (T : LightProfinite) (t : T) (n : ℕ) :
    natPoint n ≫ ninfPointSection T t = pointMap T t ≫ finiteTensorPoint T n := by
  ext u <;> rfl

@[simp]
lemma iota_comp_ninfPointSection (T : LightProfinite) (t : T) :
    ι ≫ ninfPointSection T t = pointMap T t ≫ inftyTensorPoint T := by
  ext u <;> rfl

/-- A finite natural-number point is open in `ℕ∪∞`. -/
lemma finite_nat_singleton_open (n : ℕ) : IsOpen ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) := by
  simpa using (OnePoint.isOpen_image_coe (X := ℕ) (s := ({n} : Set ℕ))).2
    (isOpen_discrete _)

/-- The standard tail neighborhood `{∞} ∪ {n | N ≤ n}` is open in `ℕ∪∞`. -/
lemma ninf_tail_open (N : ℕ) :
    IsOpen ({a : ℕ∪{∞} | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n} :
      Set ℕ∪{∞}) := by
  let A : Set (ℕ∪{∞}) := {a | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n}
  have hinfty : (∞ : ℕ∪{∞}) ∈ A := by simp [A]
  have hpre : ((↑) : ℕ → ℕ∪{∞}) ⁻¹' A = {n : ℕ | N ≤ n} := by
    ext n
    simp [A]
  have hcompact : IsCompact (((↑) : ℕ → ℕ∪{∞}) ⁻¹' A)ᶜ := by
    rw [hpre]
    have hfin : Set.Finite ({n : ℕ | n < N}) := Set.finite_lt_nat N
    have hset : ({n : ℕ | N ≤ n} : Set ℕ)ᶜ = {n : ℕ | n < N} := by
      ext n
      simp [not_le]
    rw [hset]
    exact isCompact_iff_finite.mpr hfin
  have hopenpre : IsOpen (((↑) : ℕ → ℕ∪{∞}) ⁻¹' A) := by
    rw [hpre]
    exact isOpen_discrete _
  have hA : IsOpen A := (OnePoint.isOpen_iff_of_mem' hinfty).2 ⟨hcompact, hopenpre⟩
  simpa [A] using hA

/-- A sequence of continuous maps on `T` that is eventually the zero map extends continuously over
`(ℕ∪∞) × T` by the zero value at `∞`. -/
lemma continuous_ninfTensor_of_eventually_eq_zero
    {Y : Type*} [TopologicalSpace Y] [Zero Y]
    (T : LightProfinite) (f : ℕ → C(↑T.toTop, Y))
    (hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0) :
    Continuous (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) =>
      match x.1 with
      | ∞ => (0 : Y)
      | OnePoint.some n => f n x.2) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases x with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hf
      let A : Set (ℕ∪{∞}) :=
        {a | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n}
      have hmem : ((∞ : ℕ∪{∞}), t) ∈ Set.prod A Set.univ := by
        exact ⟨by simp [A], trivial⟩
      have hAopen : IsOpen A := by simpa [A] using ninf_tail_open N
      have hopen : IsOpen (Set.prod A (Set.univ : Set T)) := hAopen.prod isOpen_univ
      have h_event : (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) =>
          match x.1 with
          | ∞ => (0 : Y)
          | OnePoint.some n => f n x.2) =ᶠ[nhds ((∞ : ℕ∪{∞}), t)] fun _ => (0 : Y) := by
        filter_upwards [hopen.mem_nhds hmem] with y hy
        rcases y with ⟨a', t'⟩
        rcases hy with ⟨ha', _⟩
        rcases ha' with h_inf | ⟨n, hn_eq, hn_le⟩
        · cases h_inf
          rfl
        · cases hn_eq
          change f n t' = 0
          rw [hN n hn_le]
          rfl
      exact continuousAt_const.congr_of_eventuallyEq h_event
  | coe n =>
      have hmem : ((n : ℕ∪{∞}), t) ∈
          Set.prod ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) (Set.univ : Set T) := by
        exact ⟨rfl, trivial⟩
      have hopen : IsOpen (Set.prod ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) (Set.univ : Set T)) := by
        exact (finite_nat_singleton_open n).prod isOpen_univ
      have h_event : (fun y : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) =>
          match y.1 with
          | ∞ => (0 : Y)
          | OnePoint.some m => f m y.2) =ᶠ[nhds ((n : ℕ∪{∞}), t)] fun y => f n y.2 := by
        filter_upwards [hopen.mem_nhds hmem] with y hy
        rcases y with ⟨a', t'⟩
        have ha' : a' = (n : ℕ∪{∞}) := by simpa using hy.1
        cases ha'
        rfl
      exact (((f n).continuous.comp continuous_snd).continuousAt).congr h_event.symm

/-- A sequence of points in a topological space that is eventually zero extends continuously over
`ℕ∪∞` by the zero value at `∞`. -/
lemma continuous_ninf_of_eventually_eq_zero
    {Y : Type*} [TopologicalSpace Y] [Zero Y]
    (f : ℕ → Y) (hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0) :
    Continuous (fun x : (ℕ∪{∞} : LightProfinite) =>
      match x with
      | ∞ => (0 : Y)
      | OnePoint.some n => f n) := by
  rw [continuous_iff_continuousAt]
  intro a
  cases a using OnePoint.rec with
  | infty =>
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hf
      let A : Set (ℕ∪{∞}) :=
        {a | a = ∞ ∨ ∃ n : ℕ, a = (n : ℕ∪{∞}) ∧ N ≤ n}
      have hmem : (∞ : ℕ∪{∞}) ∈ A := by simp [A]
      have hAopen : IsOpen A := by simpa [A] using ninf_tail_open N
      have h_event : (fun x : (ℕ∪{∞} : LightProfinite) =>
          match x with
          | ∞ => (0 : Y)
          | OnePoint.some n => f n) =ᶠ[nhds (∞ : ℕ∪{∞})] fun _ => (0 : Y) := by
        filter_upwards [hAopen.mem_nhds hmem] with y hy
        rcases hy with h_inf | ⟨n, hn_eq, hn_le⟩
        · cases h_inf
          rfl
        · cases hn_eq
          exact hN n hn_le
      exact continuousAt_const.congr_of_eventuallyEq h_event
  | coe n =>
      have hmem : (n : ℕ∪{∞}) ∈ ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) := rfl
      have hopen : IsOpen ({(n : ℕ∪{∞})} : Set ℕ∪{∞}) := finite_nat_singleton_open n
      have h_event : (fun x : (ℕ∪{∞} : LightProfinite) =>
          match x with
          | ∞ => (0 : Y)
          | OnePoint.some m => f m) =ᶠ[nhds (n : ℕ∪{∞})] fun _ => f n := by
        filter_upwards [hopen.mem_nhds hmem] with y hy
        have hy' : y = (n : ℕ∪{∞}) := by simpa using hy
        cases hy'
        rfl
      exact continuousAt_const.congr_of_eventuallyEq h_event

def boundedTailFamilyCoord (k : ℕ) : LocallyConstant (ℕ∪{∞} : LightProfinite) ℤ where
  toFun x :=
    match x with
    | ∞ => 0
    | OnePoint.some n => if n ≤ k then 1 else 0
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply continuous_ninf_of_eventually_eq_zero
    exact Filter.eventually_atTop.2 ⟨k + 1, by
      intro n hn
      simp [show ¬ n ≤ k by omega]⟩

@[simp]
lemma boundedTailFamilyCoord_finite (k n : ℕ) :
    boundedTailFamilyCoord k (n : ℕ∪{∞}) = if n ≤ k then 1 else 0 := rfl

@[simp]
lemma boundedTailFamilyCoord_infty (k : ℕ) :
    boundedTailFamilyCoord k (∞ : ℕ∪{∞}) = 0 := rfl

def boundedTailFamilySection {S : LightProfinite} (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (x : BoundedIntSeqSection S) : BoundedIntSeqSection S where
  val k := (boundedTailFamilyCoord k).comap f.hom.hom * x.val k
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    refine ⟨N, ?_⟩
    intro s k
    change Int.natAbs (boundedTailFamilyCoord k (f s) * x.val k s) ≤ N
    cases hfs : f s using OnePoint.rec with
    | infty =>
        rw [boundedTailFamilyCoord_infty]
        simp
    | coe n =>
        by_cases hn : n ≤ k
        · simpa [boundedTailFamilyCoord, hn] using hN s k
        · simp [boundedTailFamilyCoord, hn]

@[simp]
lemma boundedTailFamilySection_val {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) (k : ℕ) (s : S) :
    (boundedTailFamilySection f x).val k s = boundedTailFamilyCoord k (f s) * x.val k s := rfl

noncomputable def boundedTailFamilyLinear (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) :
    boundedIntSequences.obj.obj ⟨S⟩ →ₗ[ℤ] boundedIntSequences.obj.obj ⟨S⟩ where
  toFun x := boundedTailFamilySection f (show BoundedIntSeqSection S from x)
  map_add' := by
    intro x y
    apply BoundedIntSeqSection.ext_apply
    intro k s
    change boundedTailFamilyCoord k (f s) * (x + y).val k s =
      (boundedTailFamilySection f (show BoundedIntSeqSection S from x) +
        boundedTailFamilySection f (show BoundedIntSeqSection S from y)).val k s
    rw [BoundedIntSeqSection.val_add]
    change boundedTailFamilyCoord k (f s) * (x.val k s + y.val k s) =
      boundedTailFamilyCoord k (f s) * x.val k s + boundedTailFamilyCoord k (f s) * y.val k s
    ring
  map_smul' := by
    intro a x
    apply BoundedIntSeqSection.ext_apply
    intro k s
    change boundedTailFamilyCoord k (f s) * (a • (show BoundedIntSeqSection S from x)).val k s =
      (a • boundedTailFamilySection f (show BoundedIntSeqSection S from x)).val k s
    rw [BoundedIntSeqSection.val_zsmul]
    change boundedTailFamilyCoord k (f s) * (a * x.val k s) =
      a * (boundedTailFamilyCoord k (f s) * x.val k s)
    ring

end ProjectiveGeneratorProof
end Solid
end LightCondensed
