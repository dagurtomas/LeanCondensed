module

public import LeanCondensed.Projects.FreeCondensed.LocalInjectivity

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- Functoriality of the topological free abelian group on light profinite maps. -/
noncomputable def topologicalFreeMap {S T : LightProfinite.{0}} (f : S ⟶ T) :
    topologicalFree S ⟶ topologicalFree T :=
  (TopModuleCat.free ℤ).map (LightProfinite.toTopCat.map f)

@[simp]
lemma topologicalFreeMap_single {S T : LightProfinite.{0}} (f : S ⟶ T) (s : S) :
    (topologicalFreeMap f).hom (Finsupp.single s (1 : ℤ)) = Finsupp.single (f s) (1 : ℤ) := by
  change (Finsupp.mapDomain (LightProfinite.toTopCat.map f).hom (Finsupp.single s (1 : ℤ))) =
    Finsupp.single (f s) (1 : ℤ)
  simp [Finsupp.mapDomain_single]
  rfl

/-- The induced map between represented topological free abelian groups. -/
noncomputable def topologicalFreeCondensedMap {S T : LightProfinite.{0}} (f : S ⟶ T) :
    topologicalFreeCondensed S ⟶ topologicalFreeCondensed T :=
  LightCondensed.topModuleToLightCondAbMap (topologicalFreeMap f)

/-- The section of the underlying represented condensed set induced by the topological Dirac map. -/
noncomputable def topologicalFreeDiracSection :
    S.toCondensed ⟶ (forget ℤ).obj (topologicalFreeCondensed S) :=
  (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.app S).hom ≫
    topCatToLightCondSet.map (topologicalFreeDirac S) ≫
      (LightCondensed.topModuleToLightCondAbForgetIso (topologicalFree S)).inv

@[simp]
lemma topologicalFreeDiracSection_yoneda_apply (s : S) :
    ((show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
      (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) s) =
      Finsupp.single s (1 : ℤ) := by
  rw [GrothendieckTopology.yonedaEquiv_apply]
  dsimp [topologicalFreeDiracSection, topologicalFreeDirac]
  change (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
    (LightCondensed.topModuleToLightCondAbForgetIso (topologicalFree S)).inv.hom.app ⟨S⟩
      ((topCatToLightCondSet.map ((TopModuleCat.freeAdj ℤ).unit.app S.toTop)).hom.app ⟨S⟩
        ((lightProfiniteToLightCondSetIsoTopCatToLightCondSet.hom.app S).hom.app ⟨S⟩ (𝟙 S)))) s =
      Finsupp.single s (1 : ℤ)
  rw [LightCondensed.topModuleToLightCondAbForgetIso_inv_app]
  rfl

/-- The topological Dirac section is natural in the light profinite source. -/
lemma topologicalFreeDiracSection_naturality {S T : LightProfinite.{0}} (f : S ⟶ T) :
    lightProfiniteToLightCondSet.map f ≫ topologicalFreeDiracSection T =
      topologicalFreeDiracSection S ≫ (forget ℤ).map (topologicalFreeCondensedMap f) := by
  ext U g
  letI : TopologicalSpace ((topologicalFree T).toModuleCat : Type) := (topologicalFree T).topologicalSpace
  change (show C(↑U.unop.toTop, ↑(topologicalFree T).toModuleCat) from
      (lightProfiniteToLightCondSet.map f ≫ topologicalFreeDiracSection T).hom.app U g) =
    (show C(↑U.unop.toTop, ↑(topologicalFree T).toModuleCat) from
      (topologicalFreeDiracSection S ≫ (forget ℤ).map (topologicalFreeCondensedMap f)).hom.app U g)
  let g' : C(↑U.unop.toTop, ↑S.toTop) :=
    (lightProfiniteToLightCondSetIsoTopCatToLightCondSet.hom.app S).hom.app U g
  ext u
  dsimp [topologicalFreeDiracSection, topologicalFreeCondensedMap]
  change Finsupp.single (f (g' u)) (1 : ℤ) =
    (topologicalFreeMap f).hom (Finsupp.single (g' u) (1 : ℤ))
  exact (topologicalFreeMap_single f (g' u)).symm

/-- The topological free map sends the Dirac section to the Dirac section. -/
lemma topologicalFreeCondensedMap_diracSection_apply {S T : LightProfinite.{0}} (f : S ⟶ T) :
    (topologicalFreeCondensed T).obj.map f.op
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection T)) =
      (topologicalFreeCondensedMap f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) := by
  letI : TopologicalSpace ((topologicalFree T).toModuleCat : Type) := (topologicalFree T).topologicalSpace
  change (show C(↑S.toTop, ↑(topologicalFree T).toModuleCat) from
      (topologicalFreeCondensed T).obj.map f.op
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection T))) =
    (show C(↑S.toTop, ↑(topologicalFree T).toModuleCat) from
      (topologicalFreeCondensedMap f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))
  ext s
  dsimp [topologicalFreeCondensedMap]
  change ((show C(↑T.toTop, ↑(topologicalFree T).toModuleCat) from
      (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection T)) (f s)) =
    (topologicalFreeMap f).hom
      ((show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) s)
  rw [topologicalFreeDiracSection_yoneda_apply]
  rw [topologicalFreeDiracSection_yoneda_apply]
  exact (topologicalFreeMap_single f s).symm

/-- The topological abelian group `ℤ` with its usual discrete topology. -/
abbrev discreteIntTopModule : TopModuleCat.{0} ℤ :=
  TopModuleCat.of ℤ ℤ

/-- Continuous maps into the usual topological `ℤ` are the same as locally constant integer-valued
functions, as `ModuleCat`-valued presheaves. -/
noncomputable def discreteIntTopModulePresheafIso :
    LightCondensed.topModulePresheaf discreteIntTopModule ≅
      (LightCondMod.LocallyConstant.functorToPresheaves ℤ).obj (ModuleCat.of ℤ ℤ) := by
  refine NatIso.ofComponents (fun S => ?_) ?_
  · refine LinearEquiv.toModuleIso ?_
    refine {
      toFun := fun g => ({
        toFun := fun s => g s
        isLocallyConstant := (IsLocallyConstant.iff_continuous _).mpr g.continuous } :
          LocallyConstant S.unop ℤ)
      invFun := fun f => f.toContinuousMap
      left_inv := by intro g; ext s; rfl
      right_inv := by intro f; ext s; rfl
      map_add' := by intro g h; ext s; rfl
      map_smul' := by intro r g; ext s; rfl }
  · intro S T f
    ext g
    rfl

/-- The light condensed abelian group represented by the usual topological `ℤ` is the locally
constant `ℤ`-sheaf. -/
noncomputable def discreteIntTopModuleLocallyConstantIso :
    LightCondensed.topModuleToLightCondAbObj discreteIntTopModule ≅
      (LightCondMod.LocallyConstant.functor ℤ).obj (ModuleCat.of ℤ ℤ) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso discreteIntTopModulePresheafIso

/-- The light condensed abelian group represented by the usual topological `ℤ` is the discrete
light condensed abelian group `ℤ`. -/
noncomputable def discreteIntTopModuleCondensedIso :
    LightCondensed.topModuleToLightCondAbObj discreteIntTopModule ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  discreteIntTopModuleLocallyConstantIso ≪≫
    (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)

/-- Sections of the represented topological `ℤ` as locally constant integer-valued functions. -/
noncomputable def discreteIntTopModuleSectionsEquiv (T : LightProfinite.{0}) :
    (LightCondensed.topModuleToLightCondAbObj discreteIntTopModule).obj.obj ⟨T⟩ ≃
      LocallyConstant T ℤ where
  toFun x := discreteIntTopModulePresheafIso.hom.app ⟨T⟩ x
  invFun x := discreteIntTopModulePresheafIso.inv.app ⟨T⟩ x
  left_inv x := by
    change (discreteIntTopModulePresheafIso.hom.app ⟨T⟩ ≫
      discreteIntTopModulePresheafIso.inv.app ⟨T⟩) x = x
    rw [← NatTrans.comp_app]
    simp
  right_inv x := by
    change (discreteIntTopModulePresheafIso.inv.app ⟨T⟩ ≫
      discreteIntTopModulePresheafIso.hom.app ⟨T⟩) x = x
    rw [← NatTrans.comp_app]
    simp

/-- The previous equivalence is compatible with the comparison to the discrete light condensed
abelian group `ℤ`. -/
lemma discreteIntTopModuleCondensedIso_sections (T : LightProfinite.{0})
    (x : (LightCondensed.topModuleToLightCondAbObj discreteIntTopModule).obj.obj ⟨T⟩) :
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨T⟩
      (discreteIntTopModuleCondensedIso.hom.hom.app ⟨T⟩ x) =
    discreteIntTopModuleSectionsEquiv T x := by
  dsimp [discreteIntTopModuleSectionsEquiv, discreteIntTopModuleCondensedIso,
    discreteIntTopModuleLocallyConstantIso]
  let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)
  change (e.hom ≫ e.inv).hom.app ⟨T⟩
      ((discreteIntTopModulePresheafIso.hom.app ⟨T⟩) x) =
    (discreteIntTopModulePresheafIso.hom.app ⟨T⟩) x
  rw [Iso.hom_inv_id]
  rfl

/-- The real line as a topological `ℤ`-module. -/
abbrev realTopModule : TopModuleCat.{0} ℤ :=
  TopModuleCat.of ℤ ℝ

/-- The continuous homomorphism from the topological free abelian group induced by a continuous
map from the generators to a topological `ℤ`-module. -/
noncomputable def topologicalFreeEvalTopModule
    (M : TopModuleCat.{0} ℤ)
    (f : S.toTop ⟶ (forget₂ (TopModuleCat ℤ) TopCat).obj M) :
    topologicalFree S ⟶ M :=
  ((TopModuleCat.freeAdj ℤ).homEquiv S.toTop M).symm f

@[simp]
lemma topologicalFreeEvalTopModule_single
    (M : TopModuleCat.{0} ℤ)
    (f : S.toTop ⟶ (forget₂ (TopModuleCat ℤ) TopCat).obj M) (s : S) :
    ((topologicalFreeEvalTopModule S M f).hom (Finsupp.single s (1 : ℤ)) : M) =
      (show M from f s) := by
  change (((TopModuleCat.freeAdj ℤ).homEquiv S.toTop M
    (topologicalFreeEvalTopModule S M f)) s) = f s
  simp [topologicalFreeEvalTopModule]

/-- The universal extension computes by the usual finite sum against the generators. -/
lemma topologicalFreeEvalTopModule_apply
    (M : TopModuleCat.{0} ℤ)
    (f : S.toTop ⟶ (forget₂ (TopModuleCat ℤ) TopCat).obj M)
    (μ : topologicalFree S) :
    ((topologicalFreeEvalTopModule S M f).hom μ : M) =
      ((show S →₀ ℤ from μ).sum (fun s n => n • (show M from f s)) : M) := by
  let L : (topologicalFree S) →ₗ[ℤ] M := (topologicalFreeEvalTopModule S M f).hom.toLinearMap
  let R : (topologicalFree S) →ₗ[ℤ] M :=
    Finsupp.linearCombination ℤ fun s : S => (show M from f s)
  have hLR : L = R := by
    refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
    simp [L, R]
    convert topologicalFreeEvalTopModule_single S M f s
    · rfl
    · exact @MulAction.one_smul ℤ M _
        ((Module.toDistribMulAction : DistribMulAction ℤ M).toMulAction) (show M from f s)
  calc
    ((topologicalFreeEvalTopModule S M f).hom μ : M) = R μ := by
      change L μ = R μ
      rw [hLR]
    _ = ((show S →₀ ℤ from μ).sum (fun s n => n • (show M from f s)) : M) := by
      change (Finsupp.linearCombination ℤ (fun s : S => (show M from f s))
        (show S →₀ ℤ from μ)) = _
      rw [Finsupp.linearCombination_apply]
      simp only [Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro s _
      exact Int.cast_smul_eq_zsmul ℤ ((show S →₀ ℤ from μ) s) (show M from f s)

/-- The continuous linear map out of the topological free abelian group induced by a locally
constant integer-valued function on `S`. -/
noncomputable def topologicalFreeEval (f : LocallyConstant S ℤ) :
    topologicalFree S ⟶ discreteIntTopModule :=
  ((TopModuleCat.freeAdj ℤ).homEquiv S.toTop discreteIntTopModule).symm
    (TopCat.ofHom f.toContinuousMap)

@[simp]
lemma topologicalFreeEval_single (f : LocallyConstant S ℤ) (s : S) :
    (topologicalFreeEval S f).hom (Finsupp.single s (1 : ℤ)) = f s := by
  change (((TopModuleCat.freeAdj ℤ).homEquiv S.toTop discreteIntTopModule
    (topologicalFreeEval S f)) s) = f s
  simp [topologicalFreeEval]

/-- The continuous linear evaluation map on the topological free abelian group is the usual finite
sum against the locally constant function. -/
lemma topologicalFreeEval_apply (f : LocallyConstant S ℤ) (μ : topologicalFree S) :
    (topologicalFreeEval S f).hom μ = (Finsupp.linearCombination ℤ fun s : S => f s) μ := by
  let L : (topologicalFree S) →ₗ[ℤ] ℤ := (topologicalFreeEval S f).hom.toLinearMap
  let R : (topologicalFree S) →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ fun s : S => f s
  change L μ = R μ
  suffices L = R by rw [this]
  refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
  simp [L, R]
  convert topologicalFreeEval_single S f s
  rfl

/-- Locally constant integer evaluations separate distinct points of the topological free abelian
 group. -/
lemma topologicalFreeEval_separates_points {μ ν : topologicalFree S} (hμν : μ ≠ ν) :
    ∃ f : LocallyConstant S ℤ,
      (topologicalFreeEval S f).hom μ ≠ (topologicalFreeEval S f).hom ν := by
  classical
  let μ' : S →₀ ℤ := μ
  let ν' : S →₀ ℤ := ν
  have hμν' : μ' ≠ ν' := by
    intro h
    apply hμν
    change μ' = ν'
    exact h
  obtain ⟨s₀, hs₀⟩ : ∃ s : S, μ' s ≠ ν' s := by
    by_contra h
    apply hμν'
    ext s
    by_contra hs
    exact h ⟨s, hs⟩
  let t : Finset S := μ'.support ∪ ν'.support
  have hs₀t : s₀ ∈ t := by
    by_cases hμ : μ' s₀ = 0
    · rw [Finset.mem_union]
      right
      rw [Finsupp.mem_support_iff]
      intro hν
      exact hs₀ (hμ.trans hν.symm)
    · rw [Finset.mem_union]
      left
      exact Finsupp.mem_support_iff.mpr hμ
  obtain ⟨n, hn⟩ := LightProfinite.exists_proj_injective_on_finset_points S t
  haveI : Finite (S.diagram.obj ⟨n⟩) := by
    change Finite (FintypeCat.toLightProfinite.obj (S.fintypeDiagram.obj ⟨n⟩))
    infer_instance
  haveI : DiscreteTopology (S.diagram.obj ⟨n⟩) := Finite.instDiscreteTopology
  let q₀ := (S.proj n).hom.hom s₀
  let g : LocallyConstant (S.diagram.obj ⟨n⟩) ℤ :=
    ⟨fun q => if q = q₀ then (1 : ℤ) else 0, IsLocallyConstant.of_discrete _⟩
  let f : LocallyConstant S ℤ := g.comap (S.proj n).hom.hom
  have hf_s₀ : f s₀ = 1 := by
    simp [f, g, q₀]
  have hf_eq_zero {s : S} (hst : s ∈ t) (hne : s ≠ s₀) : f s = 0 := by
    have hproj : (S.proj n).hom.hom s ≠ (S.proj n).hom.hom s₀ := by
      intro hq
      apply hne
      apply hn hst hs₀t
      change (ConcreteCategory.hom (S.proj n)) s = (ConcreteCategory.hom (S.proj n)) s₀
      exact hq
    simp [f, g, q₀, hproj]
  have h_eval (η : S →₀ ℤ) (hsupp : η.support ⊆ t) :
      (topologicalFreeEval S f).hom η = η s₀ := by
    rw [topologicalFreeEval_apply, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_eq_single s₀]
    · simp [hf_s₀]
    · intro s hs hne
      have hst : s ∈ t := hsupp (Finsupp.mem_support_iff.mpr hs)
      have hfs : f s = 0 := hf_eq_zero hst hne
      simp [hfs]
    · intro hη
      simp
  refine ⟨f, ?_⟩
  have hμ : (topologicalFreeEval S f).hom μ = μ' s₀ :=
    h_eval μ' (by intro s hs; exact Finset.mem_union_left _ hs)
  have hν : (topologicalFreeEval S f).hom ν = ν' s₀ :=
    h_eval ν' (by intro s hs; exact Finset.mem_union_right _ hs)
  intro h
  exact hs₀ (hμ.symm.trans (h.trans hν))

instance topologicalFree_t2Space : T2Space (topologicalFree S) := by
  classical
  rw [t2Space_iff_nhds]
  intro μ ν hμν
  obtain ⟨f, hf⟩ := topologicalFreeEval_separates_points S hμν
  let e : topologicalFree S → ℤ := fun η => (topologicalFreeEval S f).hom η
  let U : Set (topologicalFree S) := e ⁻¹' {e μ}
  let V : Set (topologicalFree S) := e ⁻¹' {e ν}
  have he : Continuous e := (topologicalFreeEval S f).hom.continuous
  refine ⟨U, ?_, V, ?_, ?_⟩
  · exact (he.isOpen_preimage _ (isOpen_discrete _)).mem_nhds rfl
  · exact (he.isOpen_preimage _ (isOpen_discrete _)).mem_nhds rfl
  · rw [Set.disjoint_left]
    intro η hηU hηV
    apply hf
    exact hηU.symm.trans hηV

/-- The real continuous linear functional on bounded continuous functions induced by a finitely
supported integer measure. -/
noncomputable def finsuppRealEvalCLM (μ : S →₀ ℤ) :
    (S →ᵇ ℝ) →L[ℝ] ℝ :=
  μ.sum fun s n => (n : ℝ) • BoundedContinuousFunction.evalCLM ℝ s

@[simp]
lemma finsuppRealEvalCLM_apply (μ : S →₀ ℤ) (f : S →ᵇ ℝ) :
    finsuppRealEvalCLM S μ f = μ.sum (fun s n => (n : ℝ) * f s) := by
  simp only [finsuppRealEvalCLM, Finsupp.sum]
  change ((∑ x ∈ μ.support, (μ x : ℝ) • BoundedContinuousFunction.evalCLM ℝ x :
      (S →ᵇ ℝ) →L[ℝ] ℝ) : (S →ᵇ ℝ) → ℝ) f =
    ∑ x ∈ μ.support, (μ x : ℝ) * f x
  simp

lemma finsuppRealEvalCLM_bound (μ : S →₀ ℤ) (f : S →ᵇ ℝ) :
    ‖finsuppRealEvalCLM S μ f‖ ≤
      (LightProfinite.FreeImage.totalVariation μ : ℝ) * ‖f‖ := by
  rw [finsuppRealEvalCLM_apply]
  rw [Real.norm_eq_abs]
  simp only [Finsupp.sum]
  calc
    |∑ x ∈ μ.support, (μ x : ℝ) * f x| ≤
        ∑ x ∈ μ.support, |(μ x : ℝ) * f x| := by
      exact Finset.abs_sum_le_sum_abs (s := μ.support) (f := fun x => (μ x : ℝ) * f x)
    _ = ∑ x ∈ μ.support, |(μ x : ℝ)| * ‖f x‖ := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [abs_mul, Real.norm_eq_abs]
    _ ≤ ∑ x ∈ μ.support, |(μ x : ℝ)| * ‖f‖ := by
      refine Finset.sum_le_sum ?_
      intro x _
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm f x)
        (abs_nonneg _)
    _ = (LightProfinite.FreeImage.totalVariation μ : ℝ) * ‖f‖ := by
      rw [LightProfinite.FreeImage.totalVariation, Finsupp.sum]
      simp_rw [Int.cast_sum, Int.cast_abs]
      rw [Finset.sum_mul]

lemma norm_finsuppRealEvalCLM_le (μ : S →₀ ℤ) :
    ‖finsuppRealEvalCLM S μ‖ ≤ (LightProfinite.FreeImage.totalVariation μ : ℝ) := by
  exact ContinuousLinearMap.opNorm_le_bound _
    (by exact_mod_cast LightProfinite.FreeImage.totalVariation_nonneg μ)
    (finsuppRealEvalCLM_bound S μ)

lemma exists_finsuppRealEvalCLM_sign (μ : S →₀ ℤ) :
    ∃ f : S →ᵇ ℝ, ‖f‖ ≤ 1 ∧
      finsuppRealEvalCLM S μ f = (LightProfinite.FreeImage.totalVariation μ : ℝ) := by
  classical
  obtain ⟨n, hn⟩ := LightProfinite.exists_proj_injective_on_finset_points S μ.support
  haveI : Finite (S.diagram.obj ⟨n⟩) := by
    change Finite (FintypeCat.toLightProfinite.obj (S.fintypeDiagram.obj ⟨n⟩))
    infer_instance
  haveI : DiscreteTopology (S.diagram.obj ⟨n⟩) := Finite.instDiscreteTopology
  let qC : C(S, S.diagram.obj ⟨n⟩) := (S.proj n).hom.hom
  let q : S → S.diagram.obj ⟨n⟩ := qC
  let μq : (S.diagram.obj ⟨n⟩) →₀ ℤ := Finsupp.mapDomain q μ
  let g : S.diagram.obj ⟨n⟩ → ℝ :=
    fun x => if 0 < μq x then 1 else if μq x < 0 then -1 else 0
  let gLC : LocallyConstant (S.diagram.obj ⟨n⟩) ℝ :=
    ⟨g, IsLocallyConstant.of_discrete g⟩
  let fLC : LocallyConstant S ℝ := gLC.comap qC
  let f : S →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact fLC.toContinuousMap
  have hμq (s : S) (hs : s ∈ μ.support) : μq (q s) = μ s := by
    exact Finsupp.mapDomain_apply' (↑μ.support : Set S) μ (by intro x hx; exact hx) hn hs
  have hf_apply (s : S) : f s = g (q s) := rfl
  have hf_support (s : S) (hs : s ∈ μ.support) :
      f s = (if 0 < μ s then (1 : ℝ) else (-1 : ℝ)) := by
    have hne : μ s ≠ 0 := Finsupp.mem_support_iff.mp hs
    by_cases hpos : 0 < μ s
    · have hqpos : 0 < μq (q s) := by simpa [hμq s hs] using hpos
      simp [hf_apply, g, hqpos, hpos]
    · have hneg : μ s < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
      have hqnot : ¬ 0 < μq (q s) := by simpa [hμq s hs] using hpos
      have hqneg : μq (q s) < 0 := by simpa [hμq s hs] using hneg
      simp [hf_apply, g, hqnot, hqneg, hpos]
  have hf_norm : ‖f‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le zero_le_one).2
    intro s
    rw [hf_apply]
    by_cases hpos : 0 < μq (q s)
    · simp [g, hpos]
    · by_cases hneg : μq (q s) < 0
      · simp [g, hpos, hneg]
      · simp [g, hpos, hneg]
  refine ⟨f, hf_norm, ?_⟩
  rw [finsuppRealEvalCLM_apply, LightProfinite.FreeImage.totalVariation]
  simp only [Finsupp.sum]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [hf_support s hs]
  by_cases hpos : 0 < μ s
  · have hnonneg : 0 ≤ μ s := le_of_lt hpos
    simp [hpos, abs_of_nonneg hnonneg]
  · have hne : μ s ≠ 0 := Finsupp.mem_support_iff.mp hs
    have hneg : μ s < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    have hnonpos : μ s ≤ 0 := le_of_lt hneg
    simp [hpos, abs_of_nonpos hnonpos]

lemma totalVariation_le_norm_finsuppRealEvalCLM (μ : S →₀ ℤ) :
    (LightProfinite.FreeImage.totalVariation μ : ℝ) ≤ ‖finsuppRealEvalCLM S μ‖ := by
  obtain ⟨f, hf_norm, hf_eval⟩ := exists_finsuppRealEvalCLM_sign S μ
  have h_eval_norm : ‖finsuppRealEvalCLM S μ f‖ =
      (LightProfinite.FreeImage.totalVariation μ : ℝ) := by
    rw [hf_eval, Real.norm_of_nonneg]
    exact_mod_cast LightProfinite.FreeImage.totalVariation_nonneg μ
  rw [← h_eval_norm]
  simpa using (finsuppRealEvalCLM S μ).le_opNorm_of_le hf_norm

lemma norm_finsuppRealEvalCLM (μ : S →₀ ℤ) :
    ‖finsuppRealEvalCLM S μ‖ = (LightProfinite.FreeImage.totalVariation μ : ℝ) := by
  exact le_antisymm (norm_finsuppRealEvalCLM_le S μ)
    (totalVariation_le_norm_finsuppRealEvalCLM S μ)

/-- The universal continuous evaluation at a bounded real-valued function agrees with the
corresponding continuous linear functional on bounded continuous functions. -/
lemma topologicalFreeEvalTopModule_real_apply_eq_finsuppRealEvalCLM
    (μ : topologicalFree S) (f : S →ᵇ ℝ) :
    ((topologicalFreeEvalTopModule S realTopModule (TopCat.ofHom f.toContinuousMap)).hom μ : ℝ) =
      finsuppRealEvalCLM S (show S →₀ ℤ from μ) f := by
  rw [topologicalFreeEvalTopModule_apply, finsuppRealEvalCLM_apply]
  simp [realTopModule]

/-- A convergent sequence in the topological free abelian group has eventually bounded total
variation. -/
lemma topologicalFree_tendsto_totalVariation_bddAbove
    {μ : ℕ → topologicalFree S} {μ₀ : topologicalFree S}
    (hμ : Filter.Tendsto μ Filter.atTop (nhds μ₀)) :
    ∃ N : ℕ, ∀ᶠ n in Filter.atTop,
      LightProfinite.FreeImage.totalVariation (μ n) ≤ (N : ℤ) := by
  classical
  let T : ℕ → (S →ᵇ ℝ) →L[ℝ] ℝ := fun n => finsuppRealEvalCLM S (μ n)
  have h_pointwise : ∀ f : S →ᵇ ℝ, ∃ C : ℝ, ∀ n : ℕ, ‖T n f‖ ≤ C := by
    intro f
    let e : topologicalFree S ⟶ realTopModule :=
      topologicalFreeEvalTopModule S realTopModule (TopCat.ofHom f.toContinuousMap)
    have he_tendsto : Filter.Tendsto (fun n : ℕ => (e.hom (μ n) : ℝ)) Filter.atTop
        (nhds (e.hom μ₀ : ℝ)) := by
      exact (e.hom.continuous.tendsto μ₀).comp hμ
    have hT_tendsto : Filter.Tendsto (fun n : ℕ => T n f) Filter.atTop
        (nhds (finsuppRealEvalCLM S (show S →₀ ℤ from μ₀) f)) := by
      rw [← topologicalFreeEvalTopModule_real_apply_eq_finsuppRealEvalCLM S μ₀ f]
      change Filter.Tendsto
        (fun n : ℕ => finsuppRealEvalCLM S (show S →₀ ℤ from μ n) f) Filter.atTop
        (nhds ((topologicalFreeEvalTopModule S realTopModule
          (TopCat.ofHom f.toContinuousMap)).hom μ₀ : ℝ))
      refine he_tendsto.congr ?_
      intro n
      exact topologicalFreeEvalTopModule_real_apply_eq_finsuppRealEvalCLM S (μ n) f
    have hnorm : Filter.Tendsto (fun n : ℕ => ‖T n f‖) Filter.atTop
        (nhds ‖finsuppRealEvalCLM S (show S →₀ ℤ from μ₀) f‖) :=
      tendsto_norm.comp hT_tendsto
    rcases hnorm.bddAbove_range with ⟨C, hC⟩
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := T) h_pointwise
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, Filter.Eventually.of_forall ?_⟩
  intro n
  have hTV_real : (LightProfinite.FreeImage.totalVariation (μ n) : ℝ) ≤ (N : ℝ) := by
    rw [← norm_finsuppRealEvalCLM S (show S →₀ ℤ from μ n)]
    exact (hC n).trans hN
  exact_mod_cast hTV_real

/-- The total variation of a continuous family of finitely supported measures over a light
profinite source is uniformly bounded. -/
lemma topologicalFree_totalVariation_bounded_of_continuous
    (U : LightProfinite.{0}) (a : (topologicalFreePresheaf S).obj ⟨U⟩) :
    ∃ N : ℕ, ∀ u : U,
      LightProfinite.FreeImage.totalVariation
        ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a) u) ≤ (N : ℤ) := by
  classical
  by_contra h
  push Not at h
  choose u hu using h
  obtain ⟨u₀, φ, hφ_mono, hφ_tendsto⟩ := CompactSpace.tendsto_subseq u
  let aC : C(↑U.toTop, ↑(topologicalFree S).toModuleCat) := a
  have ha_tendsto : Filter.Tendsto (fun n : ℕ => aC (u (φ n))) Filter.atTop (nhds (aC u₀)) := by
    exact (aC.continuous.tendsto u₀).comp hφ_tendsto
  obtain ⟨N, hN⟩ := topologicalFree_tendsto_totalVariation_bddAbove S ha_tendsto
  rcases (Filter.eventually_atTop.1 hN) with ⟨n₀, hn₀⟩
  let n := max n₀ N
  have hn_ge_n₀ : n₀ ≤ n := le_max_left _ _
  have hn_ge_N : N ≤ n := le_max_right _ _
  have h_bound : LightProfinite.FreeImage.totalVariation (aC (u (φ n))) ≤ (N : ℤ) :=
    hn₀ n hn_ge_n₀
  have hn_le_phi : n ≤ φ n := by
    exact (Nat.le_add_right n (φ 0)).trans (by simpa [zero_add] using hφ_mono.add_le_nat n 0)
  have hN_le_phi : (N : ℤ) ≤ (φ n : ℤ) := by
    exact_mod_cast hn_ge_N.trans hn_le_phi
  have h_large : (φ n : ℤ) < LightProfinite.FreeImage.totalVariation (aC (u (φ n))) :=
    hu (φ n)
  have hN_lt : (N : ℤ) < LightProfinite.FreeImage.totalVariation (aC (u (φ n))) :=
    lt_of_le_of_lt hN_le_phi h_large
  exact (not_lt_of_ge h_bound) hN_lt

/-- The finite set of signed tuple shapes of length at most `N`.  The Boolean value fixes the
negative sign convention: `true` means coefficient `-1`, and `false` means coefficient `1`. -/
def signedTupleIndex (N : ℕ) : Type :=
  Σ m : Fin (N + 1), (Fin m.1 → Bool)

instance signedTupleIndex_finite (N : ℕ) : Finite (signedTupleIndex N) := by
  unfold signedTupleIndex
  infer_instance

/-- The light profinite parameter space of tuples with the fixed length of a signed tuple index. -/
noncomputable def signedTupleSpace
    (S : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N) : LightProfinite.{0} :=
  LightProfinite.of (Fin i.1.1 → S)

/-- The `j`th coordinate projection from a signed tuple parameter space. -/
noncomputable def signedTupleProj
    (S : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N) (j : Fin i.1.1) :
    signedTupleSpace S i ⟶ S :=
  CompHausLike.ofHom _ ⟨fun x => x j, by
    change Continuous (fun x : Fin i.1.1 → S => x j)
    exact continuous_apply j⟩

@[simp]
lemma signedTupleProj_apply
    (S : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N) (j : Fin i.1.1)
    (x : signedTupleSpace S i) : signedTupleProj S i j x = x j := rfl

/-- Negation as a continuous endomorphism of the free topological abelian group. -/
noncomputable def topologicalFreeNeg (S : LightProfinite.{0}) :
    topologicalFree S ⟶ topologicalFree S :=
  ConcreteCategory.ofHom (C := TopModuleCat ℤ)
    (-(ContinuousLinearMap.id ℤ (↑(topologicalFree S).toModuleCat)))

/-- The finite signed-sum map attached to a signed tuple index. -/
noncomputable def signedTupleMap
    (S : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N) :
    C(↑(signedTupleSpace S i).toTop, ↑(topologicalFree S).toModuleCat) := by
  refine ⟨fun x => ∑ j : Fin i.1.1,
        Finsupp.single (x j) (if i.2 j then (-1 : ℤ) else (1 : ℤ)), ?_⟩
  apply continuous_finsetSum
  intro j _
  by_cases h : i.2 j
  · simp only [h, if_true]
    rw [show (fun x : signedTupleSpace S i =>
        (Finsupp.single (x j) (-1 : ℤ) : ↑(topologicalFree S).toModuleCat)) =
        fun x => (topologicalFreeNeg S).hom ((topologicalFreeDirac S).hom (x j)) by
      funext x
      change Finsupp.single (x j) (-1 : ℤ) = -Finsupp.single (x j) (1 : ℤ)
      simp]
    exact (topologicalFreeNeg S).hom.continuous.comp
      ((topologicalFreeDirac S).hom.continuous.comp (by
        change Continuous (fun x : Fin i.1.1 → S => x j)
        exact continuous_apply j))
  · simp only [h]
    exact (topologicalFreeDirac S).hom.continuous.comp (by
      change Continuous (fun x : Fin i.1.1 → S => x j)
      exact continuous_apply j)

lemma signedTupleMap_apply
    (S : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N)
    (x : signedTupleSpace S i) :
    signedTupleMap S i x =
      ∑ j : Fin i.1.1,
        Finsupp.single (x j) (if i.2 j then (-1 : ℤ) else (1 : ℤ)) := rfl

lemma int_signed_natAbs_sum (n : ℤ) :
    (∑ _ : Fin n.natAbs, (if n < 0 then (-1 : ℤ) else 1)) = n := by
  by_cases hneg : n < 0
  · simp only [hneg, if_true]
    rw [Finset.sum_const]
    simp only [Finset.card_fin, nsmul_eq_mul, mul_neg, mul_one]
    have hn : n = - (n.natAbs : ℤ) := by
      rcases Int.natAbs_eq n with h | h
      · have : 0 ≤ n := by rw [h]; exact Int.natCast_nonneg _
        exact (not_lt_of_ge this hneg).elim
      · exact h
    exact hn.symm
  · simp only [hneg, if_false]
    rw [Finset.sum_const]
    simp only [Finset.card_fin, nsmul_eq_mul, mul_one]
    exact Int.natAbs_of_nonneg (le_of_not_gt hneg)

lemma signedSigma_sum_eq (S : Type*) (μ : S →₀ ℤ) :
    (∑ a : (Σ s : {s // s ∈ μ.support}, Fin ((μ s.1).natAbs)),
      Finsupp.single (a.1.1 : S) (if μ a.1.1 < 0 then (-1 : ℤ) else 1)) = μ := by
  classical
  ext t
  rw [Finset.sum_apply' t]
  rw [Fintype.sum_sigma]
  by_cases ht : t ∈ μ.support
  · rw [Finset.sum_eq_single ⟨t, ht⟩]
    · simp [int_signed_natAbs_sum]
    · intro s _ hne
      have hst : (s : S) ≠ t := by
        intro h
        apply hne
        ext
        exact h
      simp [Finsupp.single_eq_of_ne (Ne.symm hst)]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · have hμt : μ t = 0 := by
      simpa [Finsupp.mem_support_iff] using ht
    rw [hμt]
    refine Finset.sum_eq_zero ?_
    intro s _
    simp [Finsupp.single_eq_of_ne (by
      intro hts
      have htmem : t ∈ μ.support := by
        rw [hts]
        exact s.2
      exact ht htmem : t ≠ (s : S))]

lemma signedSigma_card_eq_totalVariation (S : Type*) (μ : S →₀ ℤ) :
    (Fintype.card (Σ s : {s // s ∈ μ.support}, Fin ((μ s.1).natAbs)) : ℤ) =
      LightProfinite.FreeImage.totalVariation μ := by
  classical
  rw [LightProfinite.FreeImage.totalVariation, Finsupp.sum]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Nat.cast_sum]
  change (∑ x : (μ.support : Set S), ((μ (x : S)).natAbs : ℤ)) = ∑ a ∈ μ.support, |μ a|
  rw [Finset.sum_finset_coe (fun s : S => ((μ s).natAbs : ℤ)) μ.support]
  refine Finset.sum_congr rfl ?_
  intro s _
  exact (Int.abs_eq_natAbs (μ s)).symm

/-- Every finitely supported integer measure with total variation at most `N` is a fixed-sign
signed tuple sum of length at most `N`; repeated coordinates encode coefficients of larger
absolute value. -/
lemma exists_signedTuple_of_totalVariation_le
    (S : LightProfinite.{0}) {N : ℕ} (μ : S →₀ ℤ)
    (hμ : LightProfinite.FreeImage.totalVariation μ ≤ (N : ℤ)) :
    ∃ i : signedTupleIndex N, ∃ x : signedTupleSpace S i,
      signedTupleMap S i x = μ := by
  classical
  let α := Σ s : {s // s ∈ μ.support}, Fin ((μ s.1).natAbs)
  let m := Fintype.card α
  have hmTV : (m : ℤ) = LightProfinite.FreeImage.totalVariation μ := by
    dsimp [m, α]
    exact signedSigma_card_eq_totalVariation S μ
  have hmN_int : (m : ℤ) ≤ (N : ℤ) := by
    rw [hmTV]
    exact hμ
  have hmN : m ≤ N := by exact_mod_cast hmN_int
  let e : Fin m ≃ α := (Fintype.equivFin α).symm
  let i : signedTupleIndex N := ⟨⟨m, Nat.lt_succ_of_le hmN⟩,
    fun j => decide (μ ((e j).1.1) < 0)⟩
  let x : signedTupleSpace S i := fun j => (e j).1.1
  refine ⟨i, x, ?_⟩
  rw [signedTupleMap_apply]
  change (∑ j : Fin m,
      Finsupp.single ((e j).1.1 : S)
        (if decide (μ ((e j).1.1) < 0) then (-1 : ℤ) else 1)) = μ
  simp only [decide_eq_true_eq]
  rw [Equiv.sum_comp e (fun a : α =>
    Finsupp.single (a.1.1 : S) (if μ a.1.1 < 0 then (-1 : ℤ) else 1))]
  exact signedSigma_sum_eq S μ

/-- The free-presheaf section represented by a signed tuple of maps. -/
noncomputable def freePresheaf_signedTupleSection
    (S V : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N)
    (τ : V ⟶ signedTupleSpace S i) :
    (freePresheaf S).obj ⟨V⟩ :=
  ∑ j : Fin i.1.1,
    Finsupp.single (τ ≫ signedTupleProj S i j) (if i.2 j then (-1 : ℤ) else 1)

lemma freePresheafToTopologicalFreePresheaf_signedTupleSection
    (S V : LightProfinite.{0}) {N : ℕ} (i : signedTupleIndex N)
    (τ : V ⟶ signedTupleSpace S i) :
    (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩
      (freePresheaf_signedTupleSection S V i τ) =
    (show C(↑V.toTop, ↑(topologicalFree S).toModuleCat) from
      (signedTupleMap S i).comp τ.hom.hom) := by
  apply ContinuousMap.ext
  intro v
  rw [freePresheafToTopologicalFreePresheaf_apply]
  change Finsupp.mapDomain
      (fun g : S.toCondensed.obj.obj ⟨V⟩ => ((show V ⟶ S from g) v))
      (freePresheaf_signedTupleSection S V i τ) = signedTupleMap S i (τ v)
  rw [signedTupleMap_apply]
  rw [freePresheaf_signedTupleSection]
  change (Finsupp.mapDomain.addMonoidHom
      (fun g : S.toCondensed.obj.obj ⟨V⟩ => ((show V ⟶ S from g) v)))
      (∑ j : Fin i.1.1,
        Finsupp.single (τ ≫ signedTupleProj S i j) (if i.2 j then (-1 : ℤ) else 1)) =
    ∑ j : Fin i.1.1,
      Finsupp.single ((ConcreteCategory.hom τ) v j) (if i.2 j then (-1 : ℤ) else 1)
  rw [map_sum]
  simp [Finsupp.mapDomain_single]

/-- The closed equality locus in `U × signedTupleSpace S i` where a signed tuple represents the
value of a topological-free section. -/
def signedTuplePullbackSet
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) : Set (LightProfinite.of (U × signedTupleSpace S i)) :=
  {p | (show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a) p.1 =
    signedTupleMap S i p.2}

lemma signedTuplePullbackSet_isClosed
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) : IsClosed (signedTuplePullbackSet S U a i) := by
  change IsClosed {p : U × signedTupleSpace S i |
    (show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a) p.1 =
      signedTupleMap S i p.2}
  exact isClosed_eq
    ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a).continuous.comp continuous_fst)
    ((signedTupleMap S i).continuous.comp continuous_snd)

/-- The closed pullback of a topological-free section along a signed-tuple parametrization. -/
noncomputable def signedTuplePullback
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) : LightProfinite.{0} :=
  closedSubLightProfinite (signedTuplePullbackSet S U a i)
    (signedTuplePullbackSet_isClosed S U a i)

/-- Projection from the signed-tuple pullback to the original test object. -/
noncomputable def signedTuplePullbackπ
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) :
    signedTuplePullback S U a i ⟶ U := by
  let _ : CompactSpace (signedTuplePullbackSet S U a i) :=
    isCompact_iff_compactSpace.mp (signedTuplePullbackSet_isClosed S U a i).isCompact
  exact CompHausLike.ofHom _ ⟨fun v => ((v : signedTuplePullbackSet S U a i).1 :
      U × signedTupleSpace S i).1,
    continuous_fst.comp continuous_subtype_val⟩

/-- Projection from the signed-tuple pullback to the signed-tuple parameter space. -/
noncomputable def signedTuplePullbackτ
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) :
    signedTuplePullback S U a i ⟶ signedTupleSpace S i := by
  let _ : CompactSpace (signedTuplePullbackSet S U a i) :=
    isCompact_iff_compactSpace.mp (signedTuplePullbackSet_isClosed S U a i).isCompact
  exact CompHausLike.ofHom _ ⟨fun v => ((v : signedTuplePullbackSet S U a i).1 :
      U × signedTupleSpace S i).2,
    continuous_snd.comp continuous_subtype_val⟩

@[simp]
lemma signedTuplePullbackπ_apply
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) (v : signedTuplePullback S U a i) :
    signedTuplePullbackπ S U a i v = ((v : signedTuplePullbackSet S U a i).1 :
      U × signedTupleSpace S i).1 := by
  let _ : CompactSpace (signedTuplePullbackSet S U a i) :=
    isCompact_iff_compactSpace.mp (signedTuplePullbackSet_isClosed S U a i).isCompact
  change (ConcreteCategory.hom (signedTuplePullbackπ S U a i)) v = _
  rw [show ConcreteCategory.hom (signedTuplePullbackπ S U a i) =
      (⟨fun v => ((v : signedTuplePullbackSet S U a i).1 :
        U × signedTupleSpace S i).1, continuous_fst.comp continuous_subtype_val⟩ :
          C(↑(signedTuplePullback S U a i).toTop, ↑U.toTop)) by
    exact CompHausLike.hom_ofHom _ _]
  rfl

@[simp]
lemma signedTuplePullbackτ_apply
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) (v : signedTuplePullback S U a i) :
    signedTuplePullbackτ S U a i v = ((v : signedTuplePullbackSet S U a i).1 :
      U × signedTupleSpace S i).2 := by
  let _ : CompactSpace (signedTuplePullbackSet S U a i) :=
    isCompact_iff_compactSpace.mp (signedTuplePullbackSet_isClosed S U a i).isCompact
  change (ConcreteCategory.hom (signedTuplePullbackτ S U a i)) v = _
  rw [show ConcreteCategory.hom (signedTuplePullbackτ S U a i) =
      (⟨fun v => ((v : signedTuplePullbackSet S U a i).1 :
        U × signedTupleSpace S i).2, continuous_snd.comp continuous_subtype_val⟩ :
          C(↑(signedTuplePullback S U a i).toTop, ↑(signedTupleSpace S i).toTop)) by
    exact CompHausLike.hom_ofHom _ _]
  rfl

lemma signedTuplePullback_mem
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) (v : signedTuplePullback S U a i) :
    (show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a)
        (signedTuplePullbackπ S U a i v) =
      signedTupleMap S i (signedTuplePullbackτ S U a i v) := by
  rw [signedTuplePullbackπ_apply, signedTuplePullbackτ_apply]
  exact (v : signedTuplePullbackSet S U a i).2

lemma signedTuplePullback_condition
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (i : signedTupleIndex N) :
    (show C(↑(signedTuplePullback S U a i).toTop, ↑(topologicalFree S).toModuleCat) from
      (signedTupleMap S i).comp (signedTuplePullbackτ S U a i).hom.hom) =
    (show C(↑(signedTuplePullback S U a i).toTop, ↑(topologicalFree S).toModuleCat) from
      (topologicalFreePresheaf S).map (signedTuplePullbackπ S U a i).op a) := by
  apply ContinuousMap.ext
  intro v
  change signedTupleMap S i (signedTuplePullbackτ S U a i v) =
    (show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a)
      (signedTuplePullbackπ S U a i v)
  exact (signedTuplePullback_mem S U a i v).symm

lemma signedTuplePullback_jointly_surjective_of_bound
    (S U : LightProfinite.{0}) {N : ℕ}
    (a : (topologicalFreePresheaf S).obj ⟨U⟩)
    (hN : ∀ u : U,
      LightProfinite.FreeImage.totalVariation
        ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a) u) ≤ (N : ℤ)) :
    ∀ u : U, ∃ i : signedTupleIndex N,
      ∃ v : signedTuplePullback S U a i,
        signedTuplePullbackπ S U a i v = u := by
  intro u
  obtain ⟨i, x, hx⟩ := exists_signedTuple_of_totalVariation_le S
    ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from a) u) (hN u)
  refine ⟨i, ⟨⟨(u, x), hx.symm⟩, ?_⟩⟩
  rfl

/-- The compact subset of the topological free group parametrized by signed tuples of length at
most `N`. -/
def signedTupleBoundedSet (S : LightProfinite.{0}) (N : ℕ) : Set (topologicalFree S) :=
  ⋃ i : signedTupleIndex N, Set.range (fun x : signedTupleSpace S i => signedTupleMap S i x)

lemma signedTupleBoundedSet_isCompact (S : LightProfinite.{0}) (N : ℕ) :
    IsCompact (signedTupleBoundedSet S N) := by
  classical
  dsimp [signedTupleBoundedSet]
  exact isCompact_iUnion fun i => by
    simpa [Set.image_univ] using
      isCompact_univ.image (show Continuous fun x : signedTupleSpace S i => signedTupleMap S i x from
        (signedTupleMap S i).continuous)

lemma mem_signedTupleBoundedSet_of_totalVariation_le
    (S : LightProfinite.{0}) {N : ℕ} (μ : topologicalFree S)
    (hμ : LightProfinite.FreeImage.totalVariation μ ≤ (N : ℤ)) :
    μ ∈ signedTupleBoundedSet S N := by
  classical
  obtain ⟨i, x, hx⟩ := exists_signedTuple_of_totalVariation_le S
    (show S →₀ ℤ from μ) hμ
  rw [signedTupleBoundedSet]
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨x, hx⟩⟩

/-- Finite quotient projections jointly separate points of the represented topological free group. -/
lemma topologicalFree_eq_of_forall_proj_eq (S : LightProfinite.{0})
    {μ ν : topologicalFree S}
    (h : ∀ k : ℕ,
      (topologicalFreeMap (S.proj k)).hom μ = (topologicalFreeMap (S.proj k)).hom ν) :
    μ = ν := by
  classical
  let t : Finset S := (show S →₀ ℤ from μ).support ∪ (show S →₀ ℤ from ν).support
  obtain ⟨k, hk⟩ := LightProfinite.exists_proj_injective_on_finset_points S t
  apply finsupp_mapDomain_eq_of_eq_of_injOn_support_union
    (fun s : S => S.proj k s)
  · exact hk
  · change Finsupp.mapDomain (fun s : S => S.proj k s) (show S →₀ ℤ from μ) =
      Finsupp.mapDomain (fun s : S => S.proj k s) (show S →₀ ℤ from ν)
    have hk' := h k
    change Finsupp.mapDomain (fun s : S => S.proj k s) (show S →₀ ℤ from μ) =
      Finsupp.mapDomain (fun s : S => S.proj k s) (show S →₀ ℤ from ν) at hk'
    exact hk'

/-- A closed-graph criterion for maps into a compact space. -/
lemma continuous_of_isClosed_graph_of_compact {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [CompactSpace β]
    (f : α → β) (hgraph : IsClosed {p : α × β | p.2 = f p.1}) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro s hs
  let A : Set (α × β) := {p : α × β | p.2 = f p.1} ∩ Prod.snd ⁻¹' s
  have hA : IsClosed A := hgraph.inter (hs.preimage continuous_snd)
  have hpre : f ⁻¹' s = Prod.fst '' A := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, f x), ⟨rfl, hx⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      change f p.1 ∈ s
      rw [← hp.1]
      exact hp.2
  rw [hpre]
  exact isClosedMap_fst_of_compactSpace A hA

/-- On a uniformly bounded family of finite signed measures, continuity into the represented
topological free abelian group is detected by all finite quotient projections. -/
lemma topologicalFree_continuous_of_bounded_of_finiteProj
    (T X : LightProfinite.{0}) (a : X → topologicalFree T) (N : ℕ)
    (hN : ∀ x : X, LightProfinite.FreeImage.totalVariation (a x) ≤ (N : ℤ))
    (hproj : ∀ k : ℕ,
      Continuous fun x : X => (topologicalFreeMap (T.proj k)).hom (a x)) :
    Continuous a := by
  classical
  let Kset : Set (topologicalFree T) := signedTupleBoundedSet T N
  have hKcompact : IsCompact Kset := signedTupleBoundedSet_isCompact T N
  letI : CompactSpace Kset := isCompact_iff_compactSpace.mp hKcompact
  let aK : X → Kset := fun x => ⟨a x, mem_signedTupleBoundedSet_of_totalVariation_le T (a x) (hN x)⟩
  have hgraph : IsClosed {p : X × Kset | p.2 = aK p.1} := by
    have hgraph_eq : {p : X × Kset | p.2 = aK p.1} =
        ⋂ k : ℕ, {p : X × Kset |
          (topologicalFreeMap (T.proj k)).hom (p.2 : topologicalFree T) =
            (topologicalFreeMap (T.proj k)).hom (a p.1)} := by
      ext p
      constructor
      · intro hp
        change p.2 = aK p.1 at hp
        rw [Set.mem_iInter]
        intro k
        have hpval : (p.2 : topologicalFree T) = a p.1 := by
          simpa [aK] using congrArg Subtype.val hp
        change (topologicalFreeMap (T.proj k)).hom (p.2 : topologicalFree T) =
          (topologicalFreeMap (T.proj k)).hom (a p.1)
        rw [hpval]
      · intro hp
        apply Subtype.ext
        apply topologicalFree_eq_of_forall_proj_eq T
        intro k
        exact Set.mem_iInter.mp hp k
    rw [hgraph_eq]
    refine isClosed_iInter fun k => ?_
    exact isClosed_eq
      ((topologicalFreeMap (T.proj k)).hom.continuous.comp
        (continuous_subtype_val.comp continuous_snd))
      ((hproj k).comp continuous_fst)
  have haK : Continuous aK := continuous_of_isClosed_graph_of_compact aK hgraph
  convert continuous_subtype_val.comp haK using 1
  ext x
  rfl

/-- The section of represented topological-free condensed group induced by a bounded family whose
finite quotient projections are continuous. -/
noncomputable def topologicalFreeSectionOfBoundedFiniteProj
    (T X : LightProfinite.{0}) (a : X → topologicalFree T) (N : ℕ)
    (hN : ∀ x : X, LightProfinite.FreeImage.totalVariation (a x) ≤ (N : ℤ))
    (hproj : ∀ k : ℕ,
      Continuous fun x : X => (topologicalFreeMap (T.proj k)).hom (a x)) :
    (topologicalFreeCondensed T).obj.obj ⟨X⟩ :=
  (⟨a, topologicalFree_continuous_of_bounded_of_finiteProj T X a N hN hproj⟩ :
    C(↑X.toTop, ↑(topologicalFree T).toModuleCat))

/-- The bounded finite-projection section is represented by the continuous map it was built from. -/
@[simp]
lemma topologicalFreeSectionOfBoundedFiniteProj_underlying
    (T X : LightProfinite.{0}) (a : X → topologicalFree T) (N : ℕ)
    (hN : ∀ x : X, LightProfinite.FreeImage.totalVariation (a x) ≤ (N : ℤ))
    (hproj : ∀ k : ℕ,
      Continuous fun x : X => (topologicalFreeMap (T.proj k)).hom (a x)) :
    (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
      topologicalFreeSectionOfBoundedFiniteProj T X a N hN hproj) =
      (⟨a, topologicalFree_continuous_of_bounded_of_finiteProj T X a N hN hproj⟩ :
        C(↑X.toTop, ↑(topologicalFree T).toModuleCat)) :=
  rfl

/-- Pointwise form of `topologicalFreeSectionOfBoundedFiniteProj_underlying`. -/
@[simp]
lemma topologicalFreeSectionOfBoundedFiniteProj_apply
    (T X : LightProfinite.{0}) (a : X → topologicalFree T) (N : ℕ)
    (hN : ∀ x : X, LightProfinite.FreeImage.totalVariation (a x) ≤ (N : ℤ))
    (hproj : ∀ k : ℕ,
      Continuous fun x : X => (topologicalFreeMap (T.proj k)).hom (a x)) (x : X) :
    (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
      topologicalFreeSectionOfBoundedFiniteProj T X a N hN hproj) x = a x :=
  rfl

/-- Restriction of a represented topological-free section is composition with the source map. -/
@[simp]
lemma topologicalFreeCondensed_section_map_apply
    (T X Y : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩)
    (f : Y ⟶ X) (y : Y) :
    (show C(↑Y.toTop, ↑(topologicalFree T).toModuleCat) from
      (topologicalFreeCondensed T).obj.map f.op s) y =
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from s) (f y) :=
  rfl

/-- Restricting a represented topological-free section to a point evaluates its underlying map. -/
@[simp]
lemma topologicalFreeCondensed_section_map_point
    (T X : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩)
    (f : LightProfinite.of PUnit ⟶ X) (pt : LightProfinite.of PUnit) :
    (show C(↑(LightProfinite.of PUnit).toTop, ↑(topologicalFree T).toModuleCat) from
      (topologicalFreeCondensed T).obj.map f.op s) pt =
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from s) (f pt) :=
  rfl

lemma freePresheafToTopologicalFreePresheaf_imageSieve_mem
    (S U : LightProfinite.{0})
    (a : (topologicalFreePresheaf S).obj ⟨U⟩) :
    CategoryTheory.Presheaf.imageSieve
      (freePresheafToTopologicalFreePresheaf S) a ∈
        (coherentTopology LightProfinite) U := by
  obtain ⟨N, hN⟩ := topologicalFree_totalVariation_bounded_of_continuous S U a
  let V : signedTupleIndex N → LightProfinite.{0} := fun i => signedTuplePullback S U a i
  let π : (i : signedTupleIndex N) → V i ⟶ U := fun i => signedTuplePullbackπ S U a i
  refine presheaf_imageSieve_mem_of_finite_jointly_surjective
    (freePresheafToTopologicalFreePresheaf S) a V π ?_ ?_
  · exact signedTuplePullback_jointly_surjective_of_bound S U a hN
  · intro i
    refine ⟨freePresheaf_signedTupleSection S (V i) i (signedTuplePullbackτ S U a i), ?_⟩
    rw [freePresheafToTopologicalFreePresheaf_signedTupleSection]
    exact signedTuplePullback_condition S U a i

instance freePresheafToTopologicalFreePresheaf_isLocallySurjective
    (S : LightProfinite.{0}) :
    CategoryTheory.Presheaf.IsLocallySurjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  refine ⟨?_⟩
  intro U a
  exact freePresheafToTopologicalFreePresheaf_imageSieve_mem S U a

end LightCondAb
