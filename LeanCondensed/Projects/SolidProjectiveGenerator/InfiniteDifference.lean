module

public import LeanCondensed.Projects.SolidProjectiveGenerator.InfiniteTail
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma P_proj_comp_P_homMk (A : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ A) (hf : P_map ℤ ≫ f = 0) :
    P_proj ℤ ≫ P_homMk ℤ A f hf = f := by
  change cokernel.π (P_map ℤ) ≫ cokernel.desc (P_map ℤ) f hf = f
  exact cokernel.π_desc (P_map ℤ) f hf

/-- The map from the sequence object `P ℤ` to the free object on `T` used in Lemma 3.3.2. -/
noncomputable def infinitePToFree (T : LightProfinite) [Infinite T] :
    P ℤ ⟶ (free ℤ).obj T.toCondensed :=
  P_homMk ℤ ((free ℤ).obj T.toCondensed) (infinitePToFreeNumerator T)
    (infinitePToFreeNumerator_kills T)

/-- The basis element of `P ℤ` at coordinate `i`, followed by `infinitePToFree`, is the chosen
finite-stage value at `i`. -/
lemma pBasis_comp_infinitePToFree (T : LightProfinite) [Infinite T] (i : ℕ) :
    pBasis i ≫ infinitePToFree T = freePointIsoUnit.inv ≫ infinitePToFreeFiniteValue T i := by
  dsimp [pBasis, infinitePToFree]
  rw [Category.assoc]
  rw [P_proj_comp_P_homMk]
  dsimp [freeNatBasis]
  rw [Category.assoc]
  change freePointIsoUnit.inv ≫
      freeNatValue ((free ℤ).obj T.toCondensed) i (infinitePToFreeNumerator T) =
    freePointIsoUnit.inv ≫ infinitePToFreeFiniteValue T i
  rw [infinitePToFreeNumerator_finite]

/-- The tail endomorphisms in Lemma 3.3.2, packaged as a map out of `P ℤ ⊗ ℤ[T]`. -/
noncomputable def infiniteTailMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed :=
  pTensorDesc ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
    (infiniteTailNumerator T) (infiniteTailNumerator_kills T)

/-- The locally constant finite-stage index map sending a point of `T.component n` to the place
where it appears in the null enumeration of finite-stage points. -/
noncomputable def finiteDifferenceIndexMap (T : LightProfinite) [Infinite T] (n : ℕ) :
    T.component n ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun a => (finiteDifferenceIndex T ⟨n, a⟩ : ℕ∪{∞}),
    continuous_of_discreteTopology⟩

@[simp]
lemma finiteDifferenceIndexMap_apply (T : LightProfinite) [Infinite T] (n : ℕ)
    (a : T.component n) :
    finiteDifferenceIndexMap T n a =
      (finiteDifferenceIndex T ⟨n, a⟩ : ℕ∪{∞}) := rfl

/-- The `n`th finite slice of the finite-difference factorization through `P ℤ`: project to the
`n`th finite quotient, look up the corresponding enumerating coordinate of `P`, and pass to the
quotient `P ℤ`. -/
noncomputable def infiniteDifferenceFiniteSlice (T : LightProfinite) [Infinite T] (n : ℕ) :
    (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map (T.proj n ≫ finiteDifferenceIndexMap T n) ≫
    P_proj ℤ

-- The finite natural generator, followed by `P_proj` and `infinitePToFree`, gives the
-- corresponding finite value in the chosen null sequence.
set_option backward.isDefEq.respectTransparency false in
lemma freeNatMap_comp_infinitePToFree (T : LightProfinite) [Infinite T] (i : ℕ) :
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint i)) ≫ P_proj ℤ ≫
      infinitePToFree T = infinitePToFreeFiniteValue T i := by
  dsimp [infinitePToFree]
  rw [P_proj_comp_P_homMk]
  change freeNatValue ((free ℤ).obj T.toCondensed) i (infinitePToFreeNumerator T) =
    infinitePToFreeFiniteValue T i
  rw [infinitePToFreeNumerator_finite]

-- Precomposing the finite-difference slice with a point of `T` selects the corresponding
-- coordinate of `P ℤ`.
set_option backward.isDefEq.respectTransparency false in
lemma freePointMap_comp_infiniteDifferenceFiniteSlice (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ infiniteDifferenceFiniteSlice T n =
      (free ℤ).map (lightProfiniteToLightCondSet.map
        (natPoint (finiteDifferenceIndex T ⟨n, T.proj n t⟩))) ≫ P_proj ℤ := by
  dsimp [freePointMap, infiniteDifferenceFiniteSlice]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (pointMap T t) ≫
      ((lightProfiniteToLightCondSet ⋙ free ℤ).map
        (T.proj n ≫ finiteDifferenceIndexMap T n) ≫ P_proj ℤ) =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (natPoint (finiteDifferenceIndex T ⟨n, T.proj n t⟩)) ≫ P_proj ℤ
  rw [← Category.assoc]
  rw [← Functor.map_comp]
  congr 1

/-- Pointwise, the finite-difference slice followed by `infinitePToFree` is the finite-stage
value indexed by the point's finite projection. -/
lemma freePointMap_comp_infiniteDifferenceFiniteSlice_comp (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T =
      finiteDifferenceValue T n (T.proj n t) := by
  rw [← Category.assoc]
  rw [freePointMap_comp_infiniteDifferenceFiniteSlice]
  rw [Category.assoc]
  rw [freeNatMap_comp_infinitePToFree]
  rw [infinitePToFreeFiniteValue_index]

lemma freePointMap_comp_freeFiniteApproxRetraction (T : LightProfinite) (n : ℕ) (t : T) :
    freePointMap T t ≫ freeFiniteApproxRetraction T n =
      freePointMap T (LightProfinite.finiteApproxRetraction T n t) := by
  exact freePointMap_comp T T (LightProfinite.finiteApproxRetraction T n) t

@[simp]
lemma finiteApproxRetraction_apply (T : LightProfinite) (n : ℕ) (t : T) :
    LightProfinite.finiteApproxRetraction T n t = LightProfinite.projSection T n (T.proj n t) :=
  rfl

/-- The finite-stage value at the `n`th projection of a point is the pointwise value of the
finite difference of tail endomorphisms. -/
lemma finiteDifferenceValue_eq_point_tail_diff (T : LightProfinite) (n : ℕ) (t : T) :
    finiteDifferenceValue T n (T.proj n t) =
      freePointMap T t ≫ (freeTailEndomorphism T n - freeTailEndomorphism T (n + 1)) := by
  cases n with
  | zero =>
      dsimp [finiteDifferenceValue, freeTailEndomorphism]
      change freePointMap T (LightProfinite.projSection T 0 (T.proj 0 t)) =
        freePointMap T t - (freePointMap T t -
          freePointMap T t ≫ freeFiniteApproxRetraction T 0)
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [finiteApproxRetraction_apply]
      abel
  | succ m =>
      dsimp [finiteDifferenceValue, freeTailEndomorphism]
      change freePointMap T (LightProfinite.projSection T (m + 1) (T.proj (m + 1) t)) -
          freePointMap T (LightProfinite.projSection T m (T.transitionMap m (T.proj (m + 1) t))) =
        (freePointMap T t - freePointMap T t ≫ freeFiniteApproxRetraction T m) -
          (freePointMap T t - freePointMap T t ≫ freeFiniteApproxRetraction T (m + 1))
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [freePointMap_comp_freeFiniteApproxRetraction]
      rw [finiteApproxRetraction_apply]
      rw [finiteApproxRetraction_apply]
      have hproj : T.proj m t = T.transitionMap m (T.proj (m + 1) t) := by
        have hmap := congrArg (fun f : T ⟶ T.component m => f t)
          (T.proj_comp_transitionMap m)
        simpa using hmap.symm
      rw [hproj]
      abel

/-- Pointwise form of the finite-difference factorization. -/
lemma infiniteDifferenceFiniteSlice_comp_pointwise (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    freePointMap T t ≫ (infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T) =
      freePointMap T t ≫ (freeTailEndomorphism T n - freeTailEndomorphism T (n + 1)) := by
  rw [freePointMap_comp_infiniteDifferenceFiniteSlice_comp]
  rw [finiteDifferenceValue_eq_point_tail_diff]

/-- Each finite difference of tail endomorphisms factors through the chosen map
`infinitePToFree`. -/
lemma infiniteDifferenceFiniteSlice_comp (T : LightProfinite) [Infinite T] (n : ℕ) :
    infiniteDifferenceFiniteSlice T n ≫ infinitePToFree T =
      freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  apply freeTarget_hom_ext_of_points
  intro t
  exact infiniteDifferenceFiniteSlice_comp_pointwise T n t

/-- The function on `(ℕ∪∞) × T` whose finite slices record the chosen finite-difference
coordinate and whose `∞` slice is `∞`. -/
noncomputable def finiteDifferenceIndexOverNinfFun (T : LightProfinite) [Infinite T] :
    ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) → ℕ∪{∞}
  | (∞, _) => ∞
  | (OnePoint.some n, t) => (finiteDifferenceIndex T ⟨n, T.proj n t⟩ : ℕ∪{∞})

/-- The finite fiber of the finite-difference index function is one finite slice of
`(ℕ∪∞) × T`, cut out by a finite quotient of `T`. -/
lemma finiteDifferenceIndexOverNinfFun_fiber_eq (T : LightProfinite) [Infinite T] (i : ℕ) :
    {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} =
    {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (((nullFiniteDifferenceEnumeration T).seq i).1 : ℕ∪{∞}) ∧
        T.proj (((nullFiniteDifferenceEnumeration T).seq i).1) x.2 =
          ((nullFiniteDifferenceEnumeration T).seq i).2} := by
  obtain ⟨m0, b0, hseqi⟩ : ∃ m0 : ℕ, ∃ b0 : T.component m0,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m0, b0⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m0, b0⟩
    exact ⟨m0, b0, rfl⟩
  ext x
  rcases x with ⟨a, t⟩
  cases a using OnePoint.rec with
  | infty =>
      simp [finiteDifferenceIndexOverNinfFun, hseqi]
  | coe n0 =>
      constructor
      · intro h
        have hidx : finiteDifferenceIndex T ⟨n0, T.proj n0 t⟩ = i := by
          simpa [finiteDifferenceIndexOverNinfFun] using h
        have hseq := nullFiniteDifferenceEnumeration_seq_index T ⟨n0, T.proj n0 t⟩
        rw [hidx, hseqi] at hseq
        cases hseq
        exact ⟨by simp [hseqi], by rw [hseqi]⟩
      · rintro ⟨hfst, hsnd⟩
        have hn : n0 = m0 := by
          simpa [hseqi] using hfst
        cases hn
        have hp : (⟨m0, T.proj m0 t⟩ : finiteDifferencePoint T) =
            (nullFiniteDifferenceEnumeration T).seq i := by
          have hsnd' : T.proj m0 t = b0 := by
            rw [hseqi] at hsnd
            exact hsnd
          rw [hseqi]
          simp [hsnd']
        have hidx := congrArg (finiteDifferenceIndex T) hp
        rw [finiteDifferenceIndex_seq] at hidx
        simpa [finiteDifferenceIndexOverNinfFun] using hidx

/-- Finite fibers of the finite-difference index function are open. -/
lemma isOpen_finiteDifferenceIndexOverNinfFun_fiber (T : LightProfinite) [Infinite T] (i : ℕ) :
    IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
  rw [finiteDifferenceIndexOverNinfFun_fiber_eq]
  obtain ⟨m, b, hseq⟩ : ∃ m : ℕ, ∃ b : T.component m,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m, b⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m, b⟩
    exact ⟨m, b, rfl⟩
  rw [hseq]
  have hfirst : IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (m : ℕ∪{∞})} := by
    have hopen : IsOpen ({(m : ℕ∪{∞})} : Set ℕ∪{∞}) := by
      simpa using (OnePoint.isOpen_image_coe (X := ℕ) (s := ({m} : Set ℕ))).2
        (isOpen_discrete _)
    simpa [IntProof.fstMap, Set.preimage, Set.setOf_eq_eq_singleton] using
      hopen.preimage (IntProof.fstMap T).continuous
  have hsecond : IsOpen {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      T.proj m x.2 = b} := by
    letI : DiscreteTopology (T.component m) := Finite.instDiscreteTopology
    have hopen : IsOpen ({b} : Set (T.component m)) := isOpen_discrete _
    have hcont : Continuous
        (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) => T.proj m x.2) :=
      (T.proj m).hom.hom.continuous.comp (IntProof.sndMap T).continuous
    simpa [Set.preimage, Set.setOf_eq_eq_singleton] using hopen.preimage hcont
  simpa [Set.setOf_and] using hfirst.inter hsecond

/-- Finite fibers of the finite-difference index function are closed. -/
lemma isClosed_finiteDifferenceIndexOverNinfFun_fiber (T : LightProfinite) [Infinite T] (i : ℕ) :
    IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
  rw [finiteDifferenceIndexOverNinfFun_fiber_eq]
  obtain ⟨m, b, hseq⟩ : ∃ m : ℕ, ∃ b : T.component m,
      (nullFiniteDifferenceEnumeration T).seq i = (⟨m, b⟩ : finiteDifferencePoint T) := by
    rcases (nullFiniteDifferenceEnumeration T).seq i with ⟨m, b⟩
    exact ⟨m, b, rfl⟩
  rw [hseq]
  have hfirst : IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      x.1 = (m : ℕ∪{∞})} := by
    have hclosed : IsClosed ({(m : ℕ∪{∞})} : Set ℕ∪{∞}) := isClosed_singleton
    simpa [IntProof.fstMap, Set.preimage, Set.setOf_eq_eq_singleton] using
      hclosed.preimage (IntProof.fstMap T).continuous
  have hsecond : IsClosed {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
      T.proj m x.2 = b} := by
    have hclosed : IsClosed ({b} : Set (T.component m)) := isClosed_singleton
    have hcont : Continuous
        (fun x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) => T.proj m x.2) :=
      (T.proj m).hom.hom.continuous.comp (IntProof.sndMap T).continuous
    simpa [Set.preimage, Set.setOf_eq_eq_singleton] using hclosed.preimage hcont
  simpa [Set.setOf_and] using hfirst.inter hsecond

/-- The finite-difference index function is continuous.  This is the topological uniform-null part
of the AsLimit enumeration: finite output sets are hit by only finitely many finite input slices. -/
lemma continuous_finiteDifferenceIndexOverNinfFun (T : LightProfinite) [Infinite T] :
    Continuous (finiteDifferenceIndexOverNinfFun T) := by
  rw [continuous_def]
  intro s hs
  by_cases hinfty : (∞ : ℕ∪{∞}) ∈ s
  · let F : Set ℕ := (((↑) : ℕ → ℕ∪{∞}) ⁻¹' s)ᶜ
    have hcompact : IsCompact F := by
      dsimp [F]
      exact ((OnePoint.isOpen_iff_of_mem' (X := ℕ) hinfty).mp hs).1
    have hF : Set.Finite F := isCompact_iff_finite.mp hcompact
    have hpre : finiteDifferenceIndexOverNinfFun T ⁻¹' s =
        (⋃ i ∈ F, {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
          finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})})ᶜ := by
      ext x
      constructor
      · intro hx hmem
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem
        rcases hmem with ⟨i, hiF, hxi⟩
        have hi_not : (i : ℕ∪{∞}) ∉ s := hiF
        exact hi_not (hxi ▸ hx)
      · intro hx
        by_cases hfx : finiteDifferenceIndexOverNinfFun T x = (∞ : ℕ∪{∞})
        · change finiteDifferenceIndexOverNinfFun T x ∈ s
          rw [hfx]
          exact hinfty
        · rcases (OnePoint.ne_infty_iff_exists.mp hfx) with ⟨i, hi⟩
          have hnotF : i ∉ F := by
            intro hiF
            apply hx
            simp only [Set.mem_iUnion, Set.mem_setOf_eq]
            exact ⟨i, hiF, hi.symm⟩
          have hiA : i ∈ ((↑) : ℕ → ℕ∪{∞}) ⁻¹' s := by
            simpa [F] using hnotF
          change finiteDifferenceIndexOverNinfFun T x ∈ s
          rw [← hi]
          exact hiA
    rw [hpre]
    exact (hF.isClosed_biUnion fun i _ =>
      isClosed_finiteDifferenceIndexOverNinfFun_fiber T i).isOpen_compl
  · let A : Set ℕ := ((↑) : ℕ → ℕ∪{∞}) ⁻¹' s
    have hpre : finiteDifferenceIndexOverNinfFun T ⁻¹' s =
        ⋃ i ∈ A, {x : ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) |
          finiteDifferenceIndexOverNinfFun T x = (i : ℕ∪{∞})} := by
      ext x
      constructor
      · intro hx
        by_cases hfx : finiteDifferenceIndexOverNinfFun T x = (∞ : ℕ∪{∞})
        · change finiteDifferenceIndexOverNinfFun T x ∈ s at hx
          rw [hfx] at hx
          exact False.elim (hinfty hx)
        · rcases (OnePoint.ne_infty_iff_exists.mp hfx) with ⟨i, hi⟩
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          refine ⟨i, ?_, hi.symm⟩
          change finiteDifferenceIndexOverNinfFun T x ∈ s at hx
          rw [← hi] at hx
          exact hx
      · intro hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
        rcases hx with ⟨i, hiA, hxi⟩
        change finiteDifferenceIndexOverNinfFun T x ∈ s
        rw [hxi]
        exact hiA
    rw [hpre]
    exact isOpen_biUnion fun i _ => isOpen_finiteDifferenceIndexOverNinfFun_fiber T i

/-- The finite-difference index map `(ℕ∪∞) × T → ℕ∪∞`. -/
noncomputable def finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T] :
    ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨finiteDifferenceIndexOverNinfFun T,
    continuous_finiteDifferenceIndexOverNinfFun T⟩

@[simp]
lemma finiteDifferenceIndexOverNinf_finite (T : LightProfinite) [Infinite T]
    (n : ℕ) (t : T) :
    finiteDifferenceIndexOverNinf T ((n : ℕ∪{∞}), t) =
      (finiteDifferenceIndex T ⟨n, T.proj n t⟩ : ℕ∪{∞}) := rfl

@[simp]
lemma finiteDifferenceIndexOverNinf_infty (T : LightProfinite) [Infinite T] (t : T) :
    finiteDifferenceIndexOverNinf T ((∞ : ℕ∪{∞}), t) = (∞ : ℕ∪{∞}) := rfl

@[simp]
lemma finiteTensorPoint_comp_finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T]
    (n : ℕ) :
    finiteTensorPoint T n ≫ finiteDifferenceIndexOverNinf T =
      T.proj n ≫ finiteDifferenceIndexMap T n := by
  ext t
  rfl

/-- The constant map from `T` to the point `∞ ∈ ℕ∪∞`. -/
noncomputable def constInftyMap (T : LightProfinite) : T ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨fun _ => (∞ : ℕ∪{∞}), continuous_const⟩

@[simp]
lemma inftyTensorPoint_comp_finiteDifferenceIndexOverNinf (T : LightProfinite) [Infinite T] :
    inftyTensorPoint T ≫ finiteDifferenceIndexOverNinf T = constInftyMap T := by
  ext t
  rfl

lemma constInftyMap_eq (T : LightProfinite) : constInftyMap T = toPointMap T ≫ ι := by
  ext t
  rfl

/-- The constant-`∞` map dies after passing to `P ℤ`. -/
lemma free_constInftyMap_comp_P_proj (T : LightProfinite) :
    (free ℤ).map (lightProfiniteToLightCondSet.map (constInftyMap T)) ≫ P_proj ℤ = 0 := by
  rw [constInftyMap_eq]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T ≫ ι) ≫ P_proj ℤ = 0
  rw [Functor.map_comp]
  change ((lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ P_map ℤ) ≫
    P_proj ℤ = 0
  have hzero : P_map ℤ ≫ P_proj ℤ = 0 := by
    change P_map ℤ ≫ cokernel.π (P_map ℤ) = 0
    exact cokernel.condition (P_map ℤ)
  calc
    ((lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ P_map ℤ) ≫ P_proj ℤ
        = (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫
            (P_map ℤ ≫ P_proj ℤ) := by
          rw [Category.assoc]
    _ = (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ 0 := by
          exact congrArg
            (fun q => (lightProfiniteToLightCondSet ⋙ free ℤ).map (toPointMap T) ≫ q) hzero
    _ = 0 := by simp

/-- The finite-difference slices form a section of `P ℤ` over `(ℕ∪∞) × T` with zero `∞` slice,
assuming continuity of the finite-difference index map. -/
lemma exists_infiniteDifferenceElement (T : LightProfinite) [Infinite T] :
    ∃ x : (P ℤ).obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩,
      (∀ n : ℕ,
        (freeHomEquivPoints T (P ℤ)).symm
          ((P ℤ).obj.map (finiteTensorPoint T n).op x) =
            infiniteDifferenceFiniteSlice T n) ∧
      (freeHomEquivPoints T (P ℤ)).symm
        ((P ℤ).obj.map (inftyTensorPoint T).op x) = 0 := by
  let f : (free ℤ).obj (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite).toCondensed) ⟶ P ℤ :=
    (free ℤ).map (lightProfiniteToLightCondSet.map (finiteDifferenceIndexOverNinf T)) ≫ P_proj ℤ
  let x := freeHomEquivPoints (((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)) (P ℤ) f
  refine ⟨x, ?_, ?_⟩
  · intro n
    dsimp [x, f]
    rw [← freeHomEquivPoints_symm_map]
    rw [Equiv.symm_apply_apply]
    change (lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteTensorPoint T n) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteDifferenceIndexOverNinf T) ≫
          P_proj ℤ) = infiniteDifferenceFiniteSlice T n
    rw [← Category.assoc]
    rw [← Functor.map_comp]
    rw [finiteTensorPoint_comp_finiteDifferenceIndexOverNinf]
    rfl
  · dsimp [x, f]
    rw [← freeHomEquivPoints_symm_map]
    rw [Equiv.symm_apply_apply]
    change (lightProfiniteToLightCondSet ⋙ free ℤ).map (inftyTensorPoint T) ≫
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteDifferenceIndexOverNinf T) ≫
          P_proj ℤ) = 0
    rw [← Category.assoc]
    rw [← Functor.map_comp]
    rw [inftyTensorPoint_comp_finiteDifferenceIndexOverNinf]
    exact free_constInftyMap_comp_P_proj T

/-- The section of `P ℤ` over `(ℕ∪∞) × T` whose finite slices encode the finite-difference
factorization in Lemma 3.3.2 and whose `∞` slice is zero. -/
noncomputable def infiniteDifferenceElement (T : LightProfinite) [Infinite T] :
    (P ℤ).obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩ :=
  (exists_infiniteDifferenceElement T).choose

/-- Restricting `infiniteDifferenceElement` to the finite slice `n` gives the prescribed
finite-difference factor. -/
lemma infiniteDifferenceElement_finite (T : LightProfinite) [Infinite T] (n : ℕ) :
    (freeHomEquivPoints T (P ℤ)).symm
      ((P ℤ).obj.map (finiteTensorPoint T n).op (infiniteDifferenceElement T)) =
        infiniteDifferenceFiniteSlice T n :=
  ((exists_infiniteDifferenceElement T).choose_spec).1 n

/-- Restricting `infiniteDifferenceElement` to the `∞` slice gives zero. -/
lemma infiniteDifferenceElement_infty (T : LightProfinite) [Infinite T] :
    (freeHomEquivPoints T (P ℤ)).symm
      ((P ℤ).obj.map (inftyTensorPoint T).op (infiniteDifferenceElement T)) = 0 :=
  ((exists_infiniteDifferenceElement T).choose_spec).2

/-- The numerator of the finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceNumerator (T : LightProfinite) [Infinite T] :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
    (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) (P ℤ)).symm
      (infiniteDifferenceElement T)

/-- Finite slices of the finite-difference numerator are the prescribed factors through `P ℤ`. -/
lemma infiniteDifferenceNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) (P ℤ) n (infiniteDifferenceNumerator T) =
      infiniteDifferenceFiniteSlice T n := by
  rw [infiniteDifferenceNumerator, numeratorSlice_of_freeTensorElement]
  exact infiniteDifferenceElement_finite T n

/-- The finite-difference numerator has zero `∞` slice. -/
lemma infiniteDifferenceNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) (P ℤ) (infiniteDifferenceNumerator T) = 0 := by
  rw [infiniteDifferenceNumerator, inftySlice_of_freeTensorElement]
  exact infiniteDifferenceElement_infty T

/-- The finite-difference numerator vanishes on the basepoint summand. -/
lemma infiniteDifferenceNumerator_kills (T : LightProfinite) [Infinite T] :
    (P_map ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteDifferenceNumerator T = 0 :=
  numerator_kills_of_inftySlice_zero ((free ℤ).obj T.toCondensed) (P ℤ)
    (infiniteDifferenceNumerator T) (infiniteDifferenceNumerator_infty T)

/-- The finite-difference factorization in Lemma 3.3.2. -/
noncomputable def infiniteDifferenceMap (T : LightProfinite) [Infinite T] :
    P ℤ ⊗ (free ℤ).obj T.toCondensed ⟶ P ℤ :=
  pTensorDesc ((free ℤ).obj T.toCondensed) (P ℤ)
    (infiniteDifferenceNumerator T) (infiniteDifferenceNumerator_kills T)

/-- The section of the tail map in Lemma 3.3.2. -/
noncomputable def infiniteTailSection (T : LightProfinite) [Infinite T] :
    (free ℤ).obj T.toCondensed ⟶ P ℤ ⊗ (free ℤ).obj T.toCondensed :=
  tailSection T

/-- The finite slices of the shifted tail numerator are finite differences of tail
endomorphisms. -/
lemma shiftedTailNumerator_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (((oneMinusShift' ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T) =
    freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  rw [numeratorSlice_oneMinusShift']
  rw [infiniteTailNumerator_slice]
  rw [infiniteTailNumerator_slice]

/-- The `∞` slice of the shifted tail numerator is zero. -/
lemma shiftedTailNumerator_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (((oneMinusShift' ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T) = 0 := by
  rw [inftySlice_oneMinusShift']

/-- Finite slices commute with postcomposition by `infinitePToFree`. -/
lemma differenceNumerator_comp_slice (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) =
    numeratorSlice ((free ℤ).obj T.toCondensed) (P ℤ) n (infiniteDifferenceNumerator T) ≫
      infinitePToFree T := by
  rw [numeratorSlice_comp]

/-- Finite slices of the postcomposed finite-difference numerator are the finite differences of
tail endomorphisms. -/
lemma differenceNumerator_comp_slice_eq (T : LightProfinite) [Infinite T] (n : ℕ) :
    numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) =
    freeTailEndomorphism T n - freeTailEndomorphism T (n + 1) := by
  rw [differenceNumerator_comp_slice]
  rw [infiniteDifferenceNumerator_slice]
  rw [infiniteDifferenceFiniteSlice_comp]

/-- The `∞` slice of the finite-difference factorization is zero. -/
lemma differenceNumerator_comp_infty (T : LightProfinite) [Infinite T] :
    inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed)
      (infiniteDifferenceNumerator T ≫ infinitePToFree T) = 0 := by
  rw [inftySlice_comp]
  rw [infiniteDifferenceNumerator_infty]
  simp

/-- The numerator-level shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_numerator_comm (T : LightProfinite) [Infinite T] :
    (oneMinusShift' ℤ ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailNumerator T =
      infiniteDifferenceNumerator T ≫ infinitePToFree T := by
  apply freeTarget_numerator_ext_of_slices T
  · intro n
    rw [shiftedTailNumerator_slice, differenceNumerator_comp_slice_eq]
  · rw [shiftedTailNumerator_infty, differenceNumerator_comp_infty]

/-- The shift-retract square for Lemma 3.3.2. -/
lemma infiniteShiftRetract_comm (T : LightProfinite) [Infinite T] :
    ((oneMinusShift ℤ) ▷ (free ℤ).obj T.toCondensed) ≫ infiniteTailMap T =
      infiniteDifferenceMap T ≫ infinitePToFree T := by
  let M := (free ℤ).obj T.toCondensed
  haveI : Epi (P_proj ℤ ▷ M) := epi_P_proj_tensor M
  apply (cancel_epi (P_proj ℤ ▷ M)).1
  dsimp [infiniteTailMap, infiniteDifferenceMap, M]
  rw [← Category.assoc]
  rw [P_proj_tensor_oneMinusShift]
  rw [Category.assoc]
  rw [pTensorDesc_comp_proj]
  rw [← Category.assoc]
  rw [pTensorDesc_comp_proj]
  exact infiniteShiftRetract_numerator_comm T

/-- The tail-map section equation for Lemma 3.3.2. -/
lemma infiniteTailSection_fac (T : LightProfinite) [Infinite T] :
    infiniteTailSection T ≫ infiniteTailMap T = 𝟙 ((free ℤ).obj T.toCondensed) := by
  rw [infiniteTailSection, tailSection, infiniteTailMap]
  rw [pTensorDesc_slice]
  exact infiniteTailNumerator_zero T

/-- The concrete shift-retract data for Lemma 3.3.2, assembled from the named map and equation
obligations above. -/
noncomputable def solidifiedFreeShiftRetractData
    (T : LightProfinite) [Infinite T] :
    CategoryTheory.ShiftRetractData solidification where
  xObj := P ℤ ⊗ (free ℤ).obj T.toCondensed
  aObj := P ℤ
  bObj := (free ℤ).obj T.toCondensed
  s := (oneMinusShift ℤ) ▷ (free ℤ).obj T.toCondensed
  toB := infiniteTailMap T
  toA := infiniteDifferenceMap T
  g := infinitePToFree T
  comm := infiniteShiftRetract_comm T
  sect := infiniteTailSection T
  sect_fac := infiniteTailSection_fac T
  inverted := solidification_map_oneMinusShift_tensor_isIso ((free ℤ).obj T.toCondensed)

/-- For an infinite light profinite set, its solidified free representable is a retract of
`solidification.obj (P ℤ)`.  This is the heart-level retract form of Lemma 3.3.2. -/
noncomputable def solidifiedFreeRetractSolidPInfinite
    (T : LightProfinite) [Infinite T] :
    Retract
      (solidification.obj ((free ℤ).obj T.toCondensed))
      solidP :=
  (solidifiedFreeShiftRetractData T).retract

/-- Every solidified free representable is a retract of `solidification.obj (P ℤ)`, by first adding
an infinite coproduct summand. -/
noncomputable def solidifiedFreeRetractSolidP
    (S : LightProfinite) :
    Retract
      (solidification.obj ((free ℤ).obj S.toCondensed))
      solidP :=
  (freeRetractIntoInfinite S).map solidification |>.trans
    (solidifiedFreeRetractSolidPInfinite (infiniteEnvelope S))

/-- The solidification of `P ℤ` is a separator of solid abelian groups. -/
lemma solidP_isSeparator : IsSeparator solidP := by
  apply CategoryTheory.isSeparator_of_retracts_of_hom_ext
    (F := fun T : LightProfinite => solidification.obj ((free ℤ).obj T.toCondensed))
    (G := solidP)
  · intro X Y f g h
    exact solidifiedFree_hom_ext f g h
  · exact solidifiedFreeRetractSolidP

end ProjectiveGeneratorProof

/-- The countable product of copies of `ℤ` is projective in solid abelian groups. -/
instance solidProjectiveGenerator_projective : Projective solidProjectiveGenerator :=
  Projective.of_iso ProjectiveGeneratorProof.solidPIsoProduct
    (ProjectiveGeneratorProof.projective_solidP)

/-- The countable product of copies of `ℤ` is a separator/generator for solid abelian groups. -/
lemma solidProjectiveGenerator_isSeparator : IsSeparator solidProjectiveGenerator :=
  CategoryTheory.isSeparator_of_iso ProjectiveGeneratorProof.solidPIsoProduct
    ProjectiveGeneratorProof.solidP_isSeparator

end Solid
end LightCondensed
