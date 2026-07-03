module

public import LeanCondensed.Projects.SolidProjectiveGenerator.ZdiscSeparation
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- Direct bounded construction of the section over `(ℕ∪∞) × T` whose finite slices are the
tail endomorphisms and whose `∞` slice is zero. -/
lemma exists_infiniteTailElement_direct (T : LightProfinite) :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj
        ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op x) =
            freeTailEndomorphism T n) ∧
      (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op x) = 0 := by
  let X : LightProfinite := ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
  let s : (LightCondAb.topologicalFreeCondensed T).obj.obj ⟨X⟩ :=
    LightCondAb.topologicalFreeSectionOfBoundedFiniteProj T X (topologicalTailMeasure T) 2
      (topologicalTailMeasure_totalVariation_le_two T)
      (topologicalTailMeasure_finiteProj_continuous T)
  let x : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩ :=
    (LightCondAb.freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s
  refine ⟨x, ?_, ?_⟩
  · intro n
    apply (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).injective
    rw [Equiv.apply_symm_apply]
    apply LightCondAb.freeSection_map_eq_of_pointwise_measure_eq T T
    intro t
    rw [LightCondAb.freeToTopologicalFree_app_map_section_of_iso_symm]
    rw [LightCondAb.topologicalFreeCondensed_section_map_apply]
    rw [LightCondAb.topologicalFreeSectionOfBoundedFiniteProj_apply]
    rw [freeTailEndomorphism_topologicalFree_apply]
    rfl
  · apply (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).injective
    rw [Equiv.apply_symm_apply]
    change ((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op x =
      (0 : ((free ℤ).obj T.toCondensed).obj.obj ⟨T⟩)
    apply LightCondAb.freeSection_map_eq_of_pointwise_measure_eq T T
    intro t
    rw [LightCondAb.freeToTopologicalFree_app_map_section_of_iso_symm]
    rw [LightCondAb.topologicalFreeCondensed_section_map_apply]
    rw [LightCondAb.topologicalFreeSectionOfBoundedFiniteProj_apply]
    simp [topologicalTailMeasure]
    rfl

/-- The section of `ℤ[T]` over `(ℕ∪∞) × T` whose finite slices are the tail endomorphisms and
whose `∞` slice is zero. -/
noncomputable def infiniteTailElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  (exists_infiniteTailElement_direct T).choose

/-- The numerator of the tail map, built from its section over `(ℕ∪∞) × T`. -/
noncomputable def infiniteTailNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)
      ((free ℤ).obj T.toCondensed)).symm (infiniteTailElement T)

/-- Restricting `infiniteTailElement` to the finite slice `n` gives the `n`th tail
endomorphism. -/
lemma infiniteTailElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op
        (infiniteTailElement T)) =
      freeTailEndomorphism T n :=
  ((exists_infiniteTailElement_direct T).choose_spec).1 n

/-- Finite slices of the tail numerator are the prescribed tail endomorphisms. -/
lemma infiniteTailNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteTailNumerator T) = freeTailEndomorphism T n := by
  rw [infiniteTailNumerator, numeratorSlice_of_freeTensorElement]
  exact infiniteTailElement_finite T n

/-- Restricting `infiniteTailElement` to the `∞` slice gives zero. -/
lemma infiniteTailElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op
        (infiniteTailElement T)) = 0 :=
  ((exists_infiniteTailElement_direct T).choose_spec).2

/-- The `∞` slice of the tail numerator is zero. -/
lemma infiniteTailNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteTailNumerator T) = 0 := by
  rw [infiniteTailNumerator, inftySlice_of_freeTensorElement]
  exact infiniteTailElement_infty T

/-- The tail numerator vanishes on the basepoint summand, so it descends through `P ℤ ⊗ ℤ[T]`. -/
lemma infiniteTailNumerator_kills (T : LightProfinite) [Infinite T] :
    (P_map ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T = 0 :=
  numerator_kills_of_inftySlice_zero
    ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
    (infiniteTailNumerator T) (infiniteTailNumerator_infty T)

/-- The zeroth finite slice of the tail numerator is the identity. -/
lemma infiniteTailNumerator_zero (T : LightProfinite) [Infinite T] :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) 0
      (infiniteTailNumerator T) = 𝟙 ((free ℤ).obj T.toCondensed) := by
  simpa [freeTailEndomorphism] using infiniteTailNumerator_slice T 0

/-- After every fixed finite projection of `T`, the finite slices of the tail numerator are
eventually zero. -/
lemma infiniteTailNumerator_eventually_freeProj_zero (T : LightProfinite) [Infinite T] (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
        (infiniteTailNumerator T) ≫ freeProj T k = 0 := by
  filter_upwards [freeTailEndomorphism_eventually_freeProj_zero T k] with n hn
  rw [infiniteTailNumerator_slice]
  exact hn

/-- Points in the successive finite quotients whose lifted differences generate the sequence map
`P ℤ ⟶ ℤ[T]`. -/
abbrev finiteDifferencePoint (T : LightProfinite) := Σ m : ℕ, T.component m

/-- A block enumeration of the finite sets `T.component m`, with the stage tending to infinity.
The surjectivity field records that every finite-stage point is eventually included. -/
structure NullFiniteDifferenceEnumeration (T : LightProfinite) where
  seq : ℕ → finiteDifferencePoint T
  stage_eventually_ge : ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop, k ≤ (seq n).1
  surjective : Function.Surjective seq
  seq_injective : Function.Injective seq

/-- The points in all stages below a fixed bound form a finite set. -/
lemma finiteDifferencePoint_initial_finite (T : LightProfinite) (k : ℕ) :
    Set.Finite {p : finiteDifferencePoint T | p.1 < k} := by
  classical
  letI (m : ℕ) : Fintype (T.component m) := Fintype.ofFinite _
  let s : Finset (finiteDifferencePoint T) :=
    (Finset.range k).sigma (fun m => (Finset.univ : Finset (T.component m)))
  have hs : {p : finiteDifferencePoint T | p.1 < k} = (s : Set (finiteDifferencePoint T)) := by
    ext p
    constructor
    · intro hp
      rcases p with ⟨m, a⟩
      simpa [s] using hp
    · intro hp
      rcases p with ⟨m, a⟩
      simpa [s] using hp
  rw [hs]
  exact s.finite_toSet

/-- The countable type of finite-difference points is equivalent to `ℕ` for an infinite test
object. -/
noncomputable def finiteDifferencePointEquivNat (T : LightProfinite) [Infinite T] :
    ℕ ≃ finiteDifferencePoint T := by
  classical
  haveI : Countable (finiteDifferencePoint T) := inferInstance
  haveI : Infinite (finiteDifferencePoint T) := by
    let t : T := Classical.arbitrary T
    let f : ℕ → finiteDifferencePoint T := fun n => ⟨n, T.proj n t⟩
    have hf : Function.Injective f := by
      intro a b h
      exact congrArg Sigma.fst h
    exact Infinite.of_injective f hf
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ finiteDifferencePoint T))

/-- Enumerate the countable union of the successive finite quotients in finite blocks, so that the
stage index tends to infinity. -/
lemma exists_nullFiniteDifferenceEnumeration (T : LightProfinite) [Infinite T] :
    Nonempty (NullFiniteDifferenceEnumeration T) := by
  classical
  let e : ℕ ≃ finiteDifferencePoint T := finiteDifferencePointEquivNat T
  refine ⟨⟨e, ?_, e.surjective, e.injective⟩⟩
  intro k
  have hbad : Set.Finite {n : ℕ | (e n).1 < k} := by
    have hinit := finiteDifferencePoint_initial_finite T k
    simpa [Set.preimage, e] using Set.Finite.preimage (Equiv.injective e).injOn hinit
  obtain ⟨N, hN⟩ := hbad.bddAbove
  refine Filter.eventually_atTop.2 ⟨N + 1, ?_⟩
  intro n hn
  by_contra hlt
  have hnmem : n ∈ {n : ℕ | (e n).1 < k} := by
    dsimp
    omega
  have := hN hnmem
  omega

/-- A chosen null enumeration of the points in the successive finite quotients of an infinite test
object. -/
noncomputable def nullFiniteDifferenceEnumeration (T : LightProfinite) [Infinite T] :
    NullFiniteDifferenceEnumeration T :=
  Classical.choice (exists_nullFiniteDifferenceEnumeration T)

/-- A chosen index at which a finite-stage point appears in the null enumeration. -/
noncomputable def finiteDifferenceIndex (T : LightProfinite) [Infinite T]
    (p : finiteDifferencePoint T) : ℕ :=
  ((nullFiniteDifferenceEnumeration T).surjective p).choose

/-- The chosen index really enumerates the requested finite-stage point. -/
lemma nullFiniteDifferenceEnumeration_seq_index (T : LightProfinite) [Infinite T]
    (p : finiteDifferencePoint T) :
    (nullFiniteDifferenceEnumeration T).seq (finiteDifferenceIndex T p) = p :=
  ((nullFiniteDifferenceEnumeration T).surjective p).choose_spec

/-- Looking up the index of an already enumerated finite-stage point gives the original index. -/
lemma finiteDifferenceIndex_seq (T : LightProfinite) [Infinite T] (i : ℕ) :
    finiteDifferenceIndex T ((nullFiniteDifferenceEnumeration T).seq i) = i :=
  (nullFiniteDifferenceEnumeration T).seq_injective
    (nullFiniteDifferenceEnumeration_seq_index T ((nullFiniteDifferenceEnumeration T).seq i))

/-- The free point-map associated to a point in a finite stage.  Stage `0` contributes the
initial finite approximation; stage `m+1` contributes the difference between adjacent chosen
finite-stage sections. -/
noncomputable def finiteDifferenceValue (T : LightProfinite) :
    (m : ℕ) → T.component m →
      ((free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
        (free ℤ).obj T.toCondensed)
  | 0, a => freePointMap T (LightProfinite.projSection T 0 a)
  | m + 1, a =>
      freePointMap T (LightProfinite.projSection T (m + 1) a) -
        freePointMap T (LightProfinite.projSection T m (T.transitionMap m a))

/-- The finite signed measure underlying one finite-stage difference. -/
noncomputable def finiteDifferenceMeasure (T : LightProfinite) :
    (m : ℕ) → T.component m → LightCondAb.topologicalFree T
  | 0, a => Finsupp.single (LightProfinite.projSection T 0 a) (1 : ℤ)
  | m + 1, a =>
      Finsupp.single (LightProfinite.projSection T (m + 1) a) (1 : ℤ) -
        Finsupp.single (LightProfinite.projSection T m (T.transitionMap m a)) (1 : ℤ)

lemma finiteDifferenceMeasure_totalVariation_le_two (T : LightProfinite)
    (m : ℕ) (a : T.component m) :
    LightProfinite.FreeImage.totalVariation (finiteDifferenceMeasure T m a) ≤ (2 : ℤ) := by
  classical
  cases m with
  | zero => exact totalVariation_single_one_le_two (LightProfinite.projSection T 0 a)
  | succ m =>
      exact totalVariation_single_sub_single_le_two
        (LightProfinite.projSection T (m + 1) a)
        (LightProfinite.projSection T m (T.transitionMap m a))

/-- A positive-stage finite-difference measure vanishes after projection to every strictly earlier
finite quotient. -/
lemma finiteDifferenceMeasure_proj_zero (T : LightProfinite) {k m : ℕ} (h : k < m)
    (a : T.component m) :
    (LightCondAb.topologicalFreeMap (T.proj k)).hom (finiteDifferenceMeasure T m a) = 0 := by
  cases m with
  | zero => omega
  | succ m =>
      have hle : k ≤ m := by omega
      dsimp [finiteDifferenceMeasure]
      let μ₁ : LightCondAb.topologicalFree T :=
        Finsupp.single (LightProfinite.projSection T (m + 1) a) (1 : ℤ)
      let μ₂ : LightCondAb.topologicalFree T :=
        Finsupp.single (LightProfinite.projSection T m (T.transitionMap m a)) (1 : ℤ)
      change (LightCondAb.topologicalFreeMap (T.proj k)).hom (μ₁ - μ₂) = 0
      rw [((LightCondAb.topologicalFreeMap (T.proj k)).hom).map_sub]
      dsimp [μ₁, μ₂]
      rw [LightCondAb.topologicalFreeMap_single]
      rw [LightCondAb.topologicalFreeMap_single]
      change Finsupp.single (T.proj k (LightProfinite.projSection T (m + 1) a)) (1 : ℤ) -
          Finsupp.single (T.proj k (LightProfinite.projSection T m (T.transitionMap m a))) (1 : ℤ) = 0
      have h₁ : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.transitionMapLE (show k ≤ m + 1 by omega) a := by
        have hmap := congrArg (fun f : T.component (m + 1) ⟶ T.component k => f a)
          (LightProfinite.projSection_proj_le T (show k ≤ m + 1 by omega))
        simpa using hmap
      have h₂ : T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) =
          T.transitionMapLE hle (T.transitionMap m a) := by
        have hmap := congrArg
          (fun f : T.component m ⟶ T.component k => f (T.transitionMap m a))
          (LightProfinite.projSection_proj_le T hle)
        simpa using hmap
      have htrans : T.transitionMap m ≫ T.transitionMapLE hle =
          T.transitionMapLE (show k ≤ m + 1 by omega) := by
        change T.diagram.map ⟨homOfLE (Nat.le_succ m)⟩ ≫ T.diagram.map ⟨homOfLE hle⟩ =
          T.diagram.map ⟨homOfLE (show k ≤ m + 1 by omega)⟩
        rw [← T.diagram.map_comp]
        congr 1
      have hpts : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) := by
        rw [h₁, h₂]
        change T.transitionMapLE (show k ≤ m + 1 by omega) a =
          (T.transitionMap m ≫ T.transitionMapLE hle) a
        rw [htrans]
      rw [hpts]
      simp

lemma finiteDifferenceValue_topologicalFree_apply
    (T : LightProfinite) (m : ℕ) (a : T.component m) :
    (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
        (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)
          (finiteDifferenceValue T m a))) PUnit.unit =
      finiteDifferenceMeasure T m a := by
  cases m with
  | zero =>
      dsimp [finiteDifferenceValue, finiteDifferenceMeasure, freePointMap]
      exact freeMap_topologicalFree_apply (pointMap T (LightProfinite.projSection T 0 a)) PUnit.unit
  | succ m =>
      dsimp [finiteDifferenceValue, finiteDifferenceMeasure, freePointMap]
      rw [freeHomEquivPoints_sub]
      let pt : LightProfinite := LightProfinite.of PUnit.{1}
      let asec := freeHomEquivPoints pt ((free ℤ).obj T.toCondensed)
        ((free ℤ).map (lightProfiniteToLightCondSet.map
          (pointMap T (LightProfinite.projSection T (m + 1) a))))
      let bsec := freeHomEquivPoints pt ((free ℤ).obj T.toCondensed)
        ((free ℤ).map (lightProfiniteToLightCondSet.map
          (pointMap T (LightProfinite.projSection T m (T.transitionMap m a)))))
      have hmap : (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ (asec - bsec) =
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ asec -
            (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ bsec := by
        exact ((LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩).hom.map_sub asec bsec
      change (show C(↑pt.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ (asec - bsec)) PUnit.unit = _
      rw [hmap]
      change (show C(↑pt.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ asec) PUnit.unit -
        (show C(↑pt.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
          (LightCondAb.freeToTopologicalFree T).hom.app ⟨pt⟩ bsec) PUnit.unit = _
      rw [freeMap_topologicalFree_apply, freeMap_topologicalFree_apply]
      rfl

/-- A positive-stage finite difference vanishes after projection to every strictly earlier finite
quotient. -/
lemma finiteDifferenceValue_comp_freeProj_zero (T : LightProfinite) {k m : ℕ} (h : k < m)
    (a : T.component m) :
    finiteDifferenceValue T m a ≫ freeProj T k = 0 := by
  cases m with
  | zero => omega
  | succ m =>
      have hle : k ≤ m := by omega
      dsimp [finiteDifferenceValue]
      rw [Preadditive.sub_comp]
      rw [freePointMap_comp_freeProj]
      rw [freePointMap_comp_freeProj]
      have h₁ : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.transitionMapLE (show k ≤ m + 1 by omega) a := by
        have hmap := congrArg (fun f : T.component (m + 1) ⟶ T.component k => f a)
          (LightProfinite.projSection_proj_le T (show k ≤ m + 1 by omega))
        simpa using hmap
      have h₂ : T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) =
          T.transitionMapLE hle (T.transitionMap m a) := by
        have hmap := congrArg
          (fun f : T.component m ⟶ T.component k => f (T.transitionMap m a))
          (LightProfinite.projSection_proj_le T hle)
        simpa using hmap
      have htrans : T.transitionMap m ≫ T.transitionMapLE hle =
          T.transitionMapLE (show k ≤ m + 1 by omega) := by
        change T.diagram.map ⟨homOfLE (Nat.le_succ m)⟩ ≫ T.diagram.map ⟨homOfLE hle⟩ =
          T.diagram.map ⟨homOfLE (show k ≤ m + 1 by omega)⟩
        rw [← T.diagram.map_comp]
        congr 1
      have hpts : T.proj k (LightProfinite.projSection T (m + 1) a) =
          T.proj k (LightProfinite.projSection T m (T.transitionMap m a)) := by
        rw [h₁, h₂]
        change T.transitionMapLE (show k ≤ m + 1 by omega) a =
          (T.transitionMap m ≫ T.transitionMapLE hle) a
        rw [htrans]
      have hmaps := congrArg (freePointMap (T.component k)) hpts
      rw [hmaps]
      change freePointMap (T.component k)
            (T.proj k (LightProfinite.projSection T m (T.transitionMap m a))) -
          freePointMap (T.component k)
            (T.proj k (LightProfinite.projSection T m (T.transitionMap m a))) = 0
      abel

/-- The `n`th finite value of the null sequence defining the map `P ℤ ⟶ ℤ[T]`, obtained by
enumerating the successive finite-stage differences of the chosen AsLimit approximation of `T`. -/
noncomputable def infinitePToFreeFiniteValue (T : LightProfinite) [Infinite T] (n : ℕ) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶
      (free ℤ).obj T.toCondensed :=
  finiteDifferenceValue T ((nullFiniteDifferenceEnumeration T).seq n).1
    ((nullFiniteDifferenceEnumeration T).seq n).2

/-- Looking up a finite-stage point and then reading the corresponding finite value returns the
finite-stage difference attached to that point. -/
lemma infinitePToFreeFiniteValue_index (T : LightProfinite) [Infinite T] (m : ℕ)
    (a : T.component m) :
    infinitePToFreeFiniteValue T (finiteDifferenceIndex T ⟨m, a⟩) =
      finiteDifferenceValue T m a := by
  dsimp [infinitePToFreeFiniteValue]
  rw [nullFiniteDifferenceEnumeration_seq_index]

/-- The chosen finite values form a null sequence after every finite quotient of `T`. -/
lemma infinitePToFreeFiniteValue_eventually_freeProj_zero (T : LightProfinite) [Infinite T]
    (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, infinitePToFreeFiniteValue T n ≫ freeProj T k = 0 := by
  filter_upwards [(nullFiniteDifferenceEnumeration T).stage_eventually_ge (k + 1)] with n hn
  exact finiteDifferenceValue_comp_freeProj_zero T (by omega)
    ((nullFiniteDifferenceEnumeration T).seq n).2

/-- The finite signed measure underlying the `n`th value of the map `P ℤ ⟶ ℤ[T]`. -/
noncomputable def infinitePToFreeMeasure (T : LightProfinite) [Infinite T] (n : ℕ) :
    LightCondAb.topologicalFree T :=
  finiteDifferenceMeasure T ((nullFiniteDifferenceEnumeration T).seq n).1
    ((nullFiniteDifferenceEnumeration T).seq n).2

lemma infinitePToFreeMeasure_totalVariation_le_two (T : LightProfinite) [Infinite T] (n : ℕ) :
    LightProfinite.FreeImage.totalVariation (infinitePToFreeMeasure T n) ≤ (2 : ℤ) :=
  finiteDifferenceMeasure_totalVariation_le_two T ((nullFiniteDifferenceEnumeration T).seq n).1
    ((nullFiniteDifferenceEnumeration T).seq n).2

lemma infinitePToFreeMeasure_eventually_proj_zero (T : LightProfinite) [Infinite T] (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (LightCondAb.topologicalFreeMap (T.proj k)).hom (infinitePToFreeMeasure T n) = 0 := by
  filter_upwards [(nullFiniteDifferenceEnumeration T).stage_eventually_ge (k + 1)] with n hn
  exact finiteDifferenceMeasure_proj_zero T (by omega)
    ((nullFiniteDifferenceEnumeration T).seq n).2

lemma infinitePToFreeMeasure_finiteProj_continuous (T : LightProfinite) [Infinite T] (k : ℕ) :
    Continuous fun x : (ℕ∪{∞} : LightProfinite) =>
      (LightCondAb.topologicalFreeMap (T.proj k)).hom
        (match x with
        | ∞ => (0 : LightCondAb.topologicalFree T)
        | OnePoint.some n => infinitePToFreeMeasure T n) := by
  let f : ℕ → LightCondAb.topologicalFree (T.component k) := fun n =>
    (LightCondAb.topologicalFreeMap (T.proj k)).hom (infinitePToFreeMeasure T n)
  have hf : ∀ᶠ n : ℕ in Filter.atTop, f n = 0 := infinitePToFreeMeasure_eventually_proj_zero T k
  have hcont := continuous_ninf_of_eventually_eq_zero f hf
  convert hcont using 1
  ext x
  cases x using OnePoint.rec with
  | infty => simp
  | coe n => simp [f]

lemma infinitePToFreeFiniteValue_topologicalFree_apply
    (T : LightProfinite) [Infinite T] (n : ℕ) :
    (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
        (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)
          (infinitePToFreeFiniteValue T n))) PUnit.unit =
      infinitePToFreeMeasure T n := by
  dsimp [infinitePToFreeFiniteValue, infinitePToFreeMeasure]
  exact finiteDifferenceValue_topologicalFree_apply T ((nullFiniteDifferenceEnumeration T).seq n).1
    ((nullFiniteDifferenceEnumeration T).seq n).2

/-- Direct bounded construction of the section over `ℕ∪∞` whose finite values are
`infinitePToFreeFiniteValue` and whose value at `∞` is zero. -/
lemma exists_infinitePToFreeElement_direct (T : LightProfinite) [Infinite T] :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints (LightProfinite.of PUnit.{1})
          ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op x) =
            infinitePToFreeFiniteValue T n) ∧
      (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ι.op x) = 0 := by
  let X : LightProfinite := (ℕ∪{∞} : LightProfinite)
  let a : X → LightCondAb.topologicalFree T := fun x =>
    match x with
    | ∞ => 0
    | OnePoint.some n => infinitePToFreeMeasure T n
  let s : (LightCondAb.topologicalFreeCondensed T).obj.obj ⟨X⟩ :=
    LightCondAb.topologicalFreeSectionOfBoundedFiniteProj T X a 2 (by
      intro x
      cases x using OnePoint.rec with
      | infty =>
          change LightProfinite.FreeImage.totalVariation (0 : T →₀ ℤ) ≤ (2 : ℤ)
          simp [LightProfinite.FreeImage.totalVariation]
      | coe n => exact infinitePToFreeMeasure_totalVariation_le_two T n) (by
      intro k
      change Continuous fun x : (ℕ∪{∞} : LightProfinite) =>
        (LightCondAb.topologicalFreeMap (T.proj k)).hom (a x)
      convert infinitePToFreeMeasure_finiteProj_continuous T k using 1
      ext y
      cases y using OnePoint.rec <;> rfl)
  let x : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩ :=
    (LightCondAb.freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s
  refine ⟨x, ?_, ?_⟩
  · intro n
    apply (freeHomEquivPoints (LightProfinite.of PUnit.{1})
      ((free ℤ).obj T.toCondensed)).injective
    rw [Equiv.apply_symm_apply]
    apply LightCondAb.freeSection_map_eq_of_pointwise_measure_eq T (LightProfinite.of PUnit.{1})
    intro pt
    change (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
          (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op x)) pt =
      (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
          (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)
            (infinitePToFreeFiniteValue T n))) pt
    rw [LightCondAb.freeToTopologicalFree_app_map_section_of_iso_symm]
    rw [LightCondAb.topologicalFreeCondensed_section_map_point]
    rw [LightCondAb.topologicalFreeSectionOfBoundedFiniteProj_apply]
    cases pt
    rw [infinitePToFreeFiniteValue_topologicalFree_apply]
    rfl
  · apply (freeHomEquivPoints (LightProfinite.of PUnit.{1})
      ((free ℤ).obj T.toCondensed)).injective
    rw [Equiv.apply_symm_apply]
    change ((free ℤ).obj T.toCondensed).obj.map ι.op x =
      (0 : ((free ℤ).obj T.toCondensed).obj.obj ⟨LightProfinite.of PUnit.{1}⟩)
    apply LightCondAb.freeSection_map_eq_of_pointwise_measure_eq T (LightProfinite.of PUnit.{1})
    intro pt
    change (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
          (((free ℤ).obj T.toCondensed).obj.map ι.op x)) pt =
      (show C(↑(LightProfinite.of PUnit.{1}).toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from
        (LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit.{1}⟩
          (0 : ((free ℤ).obj T.toCondensed).obj.obj ⟨LightProfinite.of PUnit.{1}⟩)) pt
    rw [LightCondAb.freeToTopologicalFree_app_map_section_of_iso_symm]
    rw [LightCondAb.topologicalFreeCondensed_section_map_point]
    rw [LightCondAb.topologicalFreeSectionOfBoundedFiniteProj_apply]
    cases pt
    simp [a]
    rfl

/-- The finite values `infinitePToFreeFiniteValue` form a null sequence, hence give a section over
`ℕ∪∞` with value zero at `∞`. -/
lemma exists_infinitePToFreeElement (T : LightProfinite) [Infinite T] :
    ∃ x : ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints (LightProfinite.of PUnit.{1})
          ((free ℤ).obj T.toCondensed)).symm
          (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op x) =
            infinitePToFreeFiniteValue T n) ∧
      (freeHomEquivPoints (LightProfinite.of PUnit.{1})
        ((free ℤ).obj T.toCondensed)).symm
        (((free ℤ).obj T.toCondensed).obj.map ι.op x) = 0 :=
  exists_infinitePToFreeElement_direct T

/-- The section of `ℤ[T]` over `ℕ∪∞` whose finite values enumerate the successive finite-stage
differences and whose `∞` value is zero. -/
noncomputable def infinitePToFreeElement (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj T.toCondensed).obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩ :=
  (exists_infinitePToFreeElement_direct T).choose

/-- Restricting `infinitePToFreeElement` to the finite point `n` gives the prescribed finite
value. -/
lemma infinitePToFreeElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map (natPoint n).op (infinitePToFreeElement T)) =
        infinitePToFreeFiniteValue T n :=
  ((exists_infinitePToFreeElement_direct T).choose_spec).1 n

/-- Restricting `infinitePToFreeElement` to `∞` gives zero. -/
lemma infinitePToFreeElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints (LightProfinite.of PUnit.{1}) ((free ℤ).obj T.toCondensed)).symm
      (((free ℤ).obj T.toCondensed).obj.map ι.op (infinitePToFreeElement T)) = 0 :=
  ((exists_infinitePToFreeElement_direct T).choose_spec).2

/-- The numerator of the map from the sequence object to the free object on `T`. -/
noncomputable def infinitePToFreeNumerator (T : LightProfinite) [Infinite T] :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  (freeHomEquivPoints (ℕ∪{∞}) ((free ℤ).obj T.toCondensed)).symm
    (infinitePToFreeElement T)

/-- The finite values of the numerator of `infinitePToFree` are the prescribed finite-stage
differences. -/
lemma infinitePToFreeNumerator_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    freeNatValue ((free ℤ).obj T.toCondensed) n (infinitePToFreeNumerator T) =
      infinitePToFreeFiniteValue T n := by
  dsimp [infinitePToFreeNumerator]
  rw [freeNatValue_of_freeElement]
  exact infinitePToFreeElement_finite T n

/-- The numerator of `infinitePToFree` is zero at `∞`. -/
lemma infinitePToFreeNumerator_infty (T : LightProfinite) [Infinite T] :
    freeInftyValue ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T) = 0 := by
  dsimp [infinitePToFreeNumerator]
  exact freeInftyValue_zero_of_element_infty ((free ℤ).obj T.toCondensed)
    (infinitePToFreeElement T) (infinitePToFreeElement_infty T)

/-- The numerator of `infinitePToFree` kills the basepoint summand. -/
lemma infinitePToFreeNumerator_kills (T : LightProfinite) [Infinite T] :
    P_map ℤ ≫ infinitePToFreeNumerator T = 0 :=
  freeNumerator_kills_of_inftyValue_zero ((free ℤ).obj T.toCondensed)
    (infinitePToFreeNumerator T) (infinitePToFreeNumerator_infty T)

end ProjectiveGeneratorProof
end Solid
end LightCondensed
