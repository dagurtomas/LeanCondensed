module

public import LeanCondensed.Projects.SolidProjectiveGenerator.BoundedRetract
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The clopen indicator as an integer-valued locally constant function. -/
noncomputable def clopenIndicatorInt {X : Type*} [TopologicalSpace X]
    (U : Set X) (hU : IsClopen U) : LocallyConstant X ℤ :=
  (LocallyConstant.const X (1 : ℤ)).indicator hU

@[simp]
lemma clopenIndicatorInt_of_mem {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsClopen U) {x : X} (hx : x ∈ U) :
    clopenIndicatorInt U hU x = 1 := by
  simp [clopenIndicatorInt, LocallyConstant.indicator_of_mem _ hU hx]

@[simp]
lemma clopenIndicatorInt_of_notMem {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsClopen U) {x : X} (hx : x ∉ U) :
    clopenIndicatorInt U hU x = 0 := by
  simp [clopenIndicatorInt, LocallyConstant.indicator_of_notMem _ hU hx]

/-- Evaluate a finite signed measure on a locally constant integer-valued function. -/
noncomputable def freeMeasureEval (T : LightProfinite) (f : LocallyConstant T ℤ) :
    FreeMeasure T →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun t : T => f t

lemma freeMeasureEval_apply (T : LightProfinite) (f : LocallyConstant T ℤ)
    (μ : FreeMeasure T) :
    freeMeasureEval T f μ = μ.sum fun t n => n * f t := by
  simp [freeMeasureEval, Finsupp.linearCombination_apply]

/-- If a clopen set contains `t` and avoids the rest of the support of a finite measure, then its
indicator evaluates the measure to the coefficient at `t`. -/
lemma freeMeasureEval_clopenIndicator_eq_single
    {T : LightProfinite} (δ : FreeMeasure T) {t : T}
    (U : Set T) (hU : IsClopen U) (htU : t ∈ U)
    (hU_support : ∀ u ∈ δ.support, u ≠ t → u ∉ U) :
    freeMeasureEval T (clopenIndicatorInt U hU) δ = δ t := by
  rw [freeMeasureEval_apply]
  classical
  rw [Finsupp.sum]
  change (∑ b ∈ δ.support, δ b * clopenIndicatorInt U hU b) = δ t
  calc
    (∑ b ∈ δ.support, δ b * clopenIndicatorInt U hU b)
        = δ t * clopenIndicatorInt U hU t := by
          refine Finset.sum_eq_single t ?_ ?_
          · intro b hb hbt
            have hbU : b ∉ U := hU_support b hb hbt
            simp [clopenIndicatorInt_of_notMem hU hbU]
          · intro ht_not
            have hδt : δ t = 0 := by
              simpa [Finsupp.mem_support_iff] using ht_not
            simp [hδt]
    _ = δ t := by simp [clopenIndicatorInt_of_mem hU htU]

/-- Finite signed integer measures on a light profinite set are separated by locally constant
integer-valued functions. -/
lemma freeMeasure_ext_of_eval
    {T : LightProfinite} {μ ν : FreeMeasure T}
    (h : ∀ f : LocallyConstant T ℤ,
      freeMeasureEval T f μ = freeMeasureEval T f ν) :
    μ = ν := by
  classical
  let δ : FreeMeasure T := μ - ν
  have hδ_eval : ∀ f : LocallyConstant T ℤ, freeMeasureEval T f δ = 0 := by
    intro f
    dsimp [δ]
    rw [map_sub, h f, sub_self]
  have hδ : δ = 0 := by
    by_contra hδ_ne
    have hsupport_nonempty : δ.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hsupp_empty
      apply hδ_ne
      ext t
      have ht : t ∉ δ.support := by simp [hsupp_empty]
      simpa [Finsupp.mem_support_iff] using ht
    obtain ⟨t, ht_support⟩ := hsupport_nonempty
    have ht_ne : δ t ≠ 0 := (Finsupp.mem_support_iff).1 ht_support
    obtain ⟨U, hU, htU, hUavoid⟩ :=
      LightProfinite.exists_clopen_avoiding_finset T (δ.support.erase t) (t := t) (by simp)
    have hU_support : ∀ u ∈ δ.support, u ≠ t → u ∉ U := by
      intro u hu hut
      exact hUavoid u (Finset.mem_erase.mpr ⟨hut, hu⟩)
    have heval := hδ_eval (clopenIndicatorInt U hU)
    rw [freeMeasureEval_clopenIndicator_eq_single δ U hU htU hU_support] at heval
    exact ht_ne heval
  simpa [δ, sub_eq_zero] using hδ

/-- Sections of the represented topological free abelian group are separated by the evaluations
coming from locally constant integer-valued functions on the source. -/
lemma topologicalFreeCondensed_section_ext_of_eval (T S : LightProfinite)
    {x y : (LightCondAb.topologicalFreeCondensed T).obj.obj ⟨S⟩}
    (h : ∀ f : LocallyConstant T ℤ,
      (LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨S⟩ x =
        (LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨S⟩ y) :
    x = y := by
  apply ContinuousMap.ext
  intro s
  apply freeMeasure_ext_of_eval
  intro f
  have hf := h f
  have hz := congrArg (zdiscSectionsEquiv S) hf
  dsimp [LightCondAb.topologicalFreeEvalDiscrete, zdiscSectionsEquiv] at hz
  rw [LightCondAb.discreteIntTopModuleCondensedIso_sections,
    LightCondAb.discreteIntTopModuleCondensedIso_sections] at hz
  have hs := congrArg (fun g : LocallyConstant S ℤ => g s) hz
  dsimp [LightCondAb.discreteIntTopModuleSectionsEquiv,
    LightCondAb.discreteIntTopModulePresheafIso,
    LightCondAb.topologicalFreeEvalCondensed] at hs
  change (LightCondAb.topologicalFreeEval T f).hom
      ((show C(↑S.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from x) s) =
    (LightCondAb.topologicalFreeEval T f).hom
      ((show C(↑S.toTop, ↑(LightCondAb.topologicalFree T).toModuleCat) from y) s) at hs
  rw [LightCondAb.topologicalFreeEval_apply, LightCondAb.topologicalFreeEval_apply] at hs
  simpa [freeMeasureEval] using hs

/-- Sections of the represented topological free abelian group are separated by the maps induced
from finite quotients of the source. -/
lemma topologicalFreeCondensed_section_ext_of_finite_proj (T S : LightProfinite)
    {x y : (LightCondAb.topologicalFreeCondensed T).obj.obj ⟨S⟩}
    (h : ∀ k : ℕ,
      (LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩ x =
        (LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩ y) :
    x = y := by
  apply topologicalFreeCondensed_section_ext_of_eval T S
  intro f
  obtain ⟨k, g, hg⟩ := LightProfinite.exists_locallyConstant_factor_proj T f
  have hk := congrArg
    (fun z => (LightCondAb.topologicalFreeEvalDiscrete (T.component k) g).hom.app ⟨S⟩ z)
    (h k)
  change ((LightCondAb.topologicalFreeCondensedMap (T.proj k) ≫
      LightCondAb.topologicalFreeEvalDiscrete (T.component k) g).hom.app ⟨S⟩) x =
    ((LightCondAb.topologicalFreeCondensedMap (T.proj k) ≫
      LightCondAb.topologicalFreeEvalDiscrete (T.component k) g).hom.app ⟨S⟩) y at hk
  rw [LightCondAb.topologicalFreeEvalDiscrete_naturality] at hk
  simpa [← hg] using hk

/-- The current `Zdisc`-separation hypothesis identifies the images in the represented topological
free abelian group.  The remaining missing input for the free-target separation theorem is
injectivity of `freeToTopologicalFree` on sections. -/
lemma freeToTopologicalFree_section_eq_of_zdisc_eval (T S : LightProfinite)
    {x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩}
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y) :
    (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ x =
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ y := by
  apply topologicalFreeCondensed_section_ext_of_eval T S
  intro f
  have hf := h (zdiscMapOfLocallyConstant T f)
  rw [zdiscMapOfLocallyConstant_eq_freeToTopologicalFree_eval] at hf
  change (LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨S⟩
      ((LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ x) =
    (LightCondAb.topologicalFreeEvalDiscrete T f).hom.app ⟨S⟩
      ((LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ y)
  simpa using hf

/-- The topological-free comparison is an isomorphism, so it is injective on all light profinite
sections.  The point-injectivity hypothesis is retained for compatibility with older reductions. -/
lemma freeToTopologicalFree_section_injective_of_point_injective (T S : LightProfinite)
    (_hpt : Function.Injective
      ((LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit⟩)) :
    Function.Injective ((LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

/-- The non-finite free-target separation theorem is reduced to point-injectivity of the comparison
with the represented topological free abelian group. -/
lemma freeTarget_section_ext_of_zdisc_eval_of_freeToTopologicalFree_point_injective
    (T S : LightProfinite)
    (hpt : Function.Injective
      ((LightCondAb.freeToTopologicalFree T).hom.app ⟨LightProfinite.of PUnit⟩))
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y) :
    x = y := by
  apply freeToTopologicalFree_section_injective_of_point_injective T S hpt
  exact freeToTopologicalFree_section_eq_of_zdisc_eval T S h

/-- A finite light profinite set, represented as a sheaf, is the locally constant sheaf on its
underlying finite set. -/
noncomputable def finiteToLocallyConstantIso (F : LightProfinite) [Finite F] :
    F.toCondensed ≅ LightCondSet.LocallyConstant.functor.obj F := by
  refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
  · refine { hom := ?_ }
    refine { app := ?_, naturality := ?_ }
    · intro S
      refine ↾fun g => ?_
      letI : DiscreteTopology F := Finite.instDiscreteTopology
      exact (⟨g.hom, (IsLocallyConstant.iff_continuous g.hom).mpr g.hom.hom.continuous⟩ :
        LocallyConstant S.unop F)
    · intro S T φ
      ext g
      rfl
  · refine { hom := ?_ }
    refine { app := ?_, naturality := ?_ }
    · intro S
      refine ↾fun g => ?_
      exact ConcreteCategory.ofHom g.toContinuousMap
    · intro S T φ
      ext g
      rfl
  · apply Sheaf.hom_ext
    ext S g
    rfl
  · apply Sheaf.hom_ext
    ext S g
    rfl

/-- A finite representable light condensed set is the discrete sheaf on its finite set of points. -/
noncomputable def finiteToCondensedIsoDiscreteSet (F : LightProfinite) [Finite F] :
    F.toCondensed ≅ (LightCondensed.discrete (Type _)).obj F :=
  finiteToLocallyConstantIso F ≪≫ (LightCondSet.LocallyConstant.iso.app F)

/-- The composite `discrete set, then free module` is left adjoint to evaluation at the point and
forgetting the module structure. -/
noncomputable def discreteSetFreeAdjunction :
    (LightCondensed.discrete (Type _) ⋙ LightCondensed.free ℤ) ⊣
      (LightCondensed.forget ℤ ⋙ LightCondensed.underlying (Type _)) :=
  (LightCondensed.discreteUnderlyingAdj (Type _)).comp (LightCondensed.freeForgetAdjunction ℤ)

/-- The composite `free module, then discrete module` is left adjoint to evaluation at the point and
forgetting the module structure. -/
noncomputable def freeDiscreteModuleAdjunction :
    (ModuleCat.free ℤ ⋙ LightCondensed.discrete (ModuleCat ℤ)) ⊣
      (LightCondensed.underlying (ModuleCat ℤ) ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  (ModuleCat.adj ℤ).comp (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ))

/-- Compatibility of free modules with discrete light condensed sets, by uniqueness of left
adjoints. -/
noncomputable def freeDiscreteSetIso :
    LightCondensed.discrete (Type _) ⋙ LightCondensed.free ℤ ≅
      ModuleCat.free ℤ ⋙ LightCondensed.discrete (ModuleCat ℤ) :=
  Adjunction.leftAdjointUniq discreteSetFreeAdjunction freeDiscreteModuleAdjunction

/-- The finite-rank free abelian group with basis the points of a finite light profinite set. -/
noncomputable abbrev finiteFreeDiscreteModule (F : LightProfinite) : ModuleCat ℤ :=
  ModuleCat.of ℤ (F → ℤ)

/-- The usual finite-support free module on a finite type is the module of all integer-valued
functions on that type. -/
noncomputable def finiteFreeModuleIso (F : LightProfinite) [Finite F] :
    (ModuleCat.free ℤ).obj F ≅ finiteFreeDiscreteModule F :=
  LinearEquiv.toModuleIso (Finsupp.linearEquivFunOnFinite ℤ ℤ F)

/-- For finite `F`, the sheafified free light condensed group `ℤ[F]` is the discrete finite-rank
free abelian group with basis `F`. -/
noncomputable def finiteFreeIsoDiscrete (F : LightProfinite) [Finite F] :
    (free ℤ).obj F.toCondensed ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj (finiteFreeDiscreteModule F) :=
  (LightCondensed.free ℤ).mapIso (finiteToCondensedIsoDiscreteSet F) ≪≫
    freeDiscreteSetIso.app F ≪≫
      (LightCondensed.discrete (ModuleCat ℤ)).mapIso (finiteFreeModuleIso F)

/-- The coordinate functional on the finite-rank free abelian group with basis `F`. -/
noncomputable def finiteFreeCoordHom (F : LightProfinite) (a : F) :
    finiteFreeDiscreteModule F ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom {
    toFun := fun v => v a
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

/-- Applying an isomorphism of light condensed modules is injective on sections. -/
lemma lightCondAb_iso_app_injective {A B : LightCondAb} (e : A ≅ B) (S : LightProfinite) :
    Function.Injective (e.hom.hom.app ⟨S⟩) := by
  intro x y h
  have h' := congrArg (fun z => e.inv.hom.app ⟨S⟩ z) h
  change (e.hom ≫ e.inv).hom.app ⟨S⟩ x = (e.hom ≫ e.inv).hom.app ⟨S⟩ y at h'
  simpa using h'

/-- Finite free objects are separated by their integer-valued linear functionals. -/
lemma finiteFree_section_ext_of_zdisc_eval (F S : LightProfinite) [Finite F]
    (x y : ((free ℤ).obj F.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ ψ : (free ℤ).obj F.toCondensed ⟶ Zdisc,
      ψ.hom.app ⟨S⟩ x = ψ.hom.app ⟨S⟩ y) :
    x = y := by
  let M := finiteFreeDiscreteModule F
  let e := finiteFreeIsoDiscrete F
  apply lightCondAb_iso_app_injective e S
  apply (discreteModuleSectionsEquiv S M).injective
  ext s a
  let ℓ : M ⟶ ModuleCat.of ℤ ℤ := finiteFreeCoordHom F a
  let ψ : (free ℤ).obj F.toCondensed ⟶ Zdisc :=
    e.hom ≫ (LightCondensed.discrete (ModuleCat ℤ)).map ℓ
  have hh := h ψ
  have hloc := congrArg (discreteModuleSectionsEquiv S (ModuleCat.of ℤ ℤ)) hh
  change discreteModuleSectionsEquiv S (ModuleCat.of ℤ ℤ)
      (((LightCondensed.discrete (ModuleCat ℤ)).map ℓ).hom.app ⟨S⟩
        (e.hom.hom.app ⟨S⟩ x)) =
    discreteModuleSectionsEquiv S (ModuleCat.of ℤ ℤ)
      (((LightCondensed.discrete (ModuleCat ℤ)).map ℓ).hom.app ⟨S⟩
        (e.hom.hom.app ⟨S⟩ y)) at hloc
  rw [discreteModuleSectionsEquiv_map, discreteModuleSectionsEquiv_map] at hloc
  exact congrFun (congrArg LocallyConstant.toFun hloc) s

/-- For finite light profinite sets, the comparison to the represented topological free abelian
group is injective on sections. -/
lemma freeToTopologicalFree_section_injective_finite (F S : LightProfinite) [Finite F] :
    Function.Injective ((LightCondAb.freeToTopologicalFree F).hom.app ⟨S⟩) := by
  intro x y hxy
  apply finiteFree_section_ext_of_zdisc_eval F S x y
  intro ψ
  let f : LocallyConstant F ℤ := zdiscSectionsEquiv F (freeHomEquivPoints F Zdisc ψ)
  have hψ : ψ = LightCondAb.freeToTopologicalFree F ≫ LightCondAb.topologicalFreeEvalDiscrete F f := by
    rw [← zdiscMapOfLocallyConstant_of_freeHomEquivPoints F ψ]
    exact zdiscMapOfLocallyConstant_eq_freeToTopologicalFree_eval F f
  rw [hψ]
  change (LightCondAb.topologicalFreeEvalDiscrete F f).hom.app ⟨S⟩
      ((LightCondAb.freeToTopologicalFree F).hom.app ⟨S⟩ x) =
    (LightCondAb.topologicalFreeEvalDiscrete F f).hom.app ⟨S⟩
      ((LightCondAb.freeToTopologicalFree F).hom.app ⟨S⟩ y)
  rw [hxy]

/-- Equality after mapping to the represented topological free abelian group implies equality after
all finite free projections. -/
lemma freeProj_section_eq_of_freeToTopologicalFree_eq (T S : LightProfinite)
    {x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩}
    (hxy : (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ x =
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ y)
    (k : ℕ) :
    (freeProj T k).hom.app ⟨S⟩ x = (freeProj T k).hom.app ⟨S⟩ y := by
  apply freeToTopologicalFree_section_injective_finite (T.component k) S
  have hmap := congrArg
    (fun z => (LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩ z) hxy
  change ((LightCondAb.freeToTopologicalFree T ≫
      LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩) x =
    ((LightCondAb.freeToTopologicalFree T ≫
      LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩) y at hmap
  rw [← LightCondAb.freeToTopologicalFree_naturality (T.proj k)] at hmap
  change (LightCondAb.freeToTopologicalFree (T.component k)).hom.app ⟨S⟩
      ((freeProj T k).hom.app ⟨S⟩ x) =
    (LightCondAb.freeToTopologicalFree (T.component k)).hom.app ⟨S⟩
      ((freeProj T k).hom.app ⟨S⟩ y) at hmap
  exact hmap

/-- Equality after every finite free projection implies equality after mapping to the represented
topological free abelian group. -/
lemma freeToTopologicalFree_section_eq_of_freeProj_eq (T S : LightProfinite)
    {x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩}
    (h : ∀ k : ℕ,
      (freeProj T k).hom.app ⟨S⟩ x = (freeProj T k).hom.app ⟨S⟩ y) :
    (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ x =
      (LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩ y := by
  apply topologicalFreeCondensed_section_ext_of_finite_proj T S
  intro k
  change ((LightCondAb.freeToTopologicalFree T ≫
      LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩) x =
    ((LightCondAb.freeToTopologicalFree T ≫
      LightCondAb.topologicalFreeCondensedMap (T.proj k)).hom.app ⟨S⟩) y
  rw [← LightCondAb.freeToTopologicalFree_naturality (T.proj k)]
  change (LightCondAb.freeToTopologicalFree (T.component k)).hom.app ⟨S⟩
      ((freeProj T k).hom.app ⟨S⟩ x) =
    (LightCondAb.freeToTopologicalFree (T.component k)).hom.app ⟨S⟩
      ((freeProj T k).hom.app ⟨S⟩ y)
  rw [h k]

/-- The `Zdisc`-separation hypothesis implies equality after every finite free projection. -/
lemma freeProj_section_eq_of_zdisc_eval (T S : LightProfinite)
    {x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩}
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y)
    (k : ℕ) :
    (freeProj T k).hom.app ⟨S⟩ x = (freeProj T k).hom.app ⟨S⟩ y :=
  freeProj_section_eq_of_freeToTopologicalFree_eq T S
    (freeToTopologicalFree_section_eq_of_zdisc_eval T S h) k

/-- Obligation: sections of the free object `ℤ[T]` are separated by all locally constant
integer-valued functions on `T`.  This is the non-finite free-object separation input used to pass
from all finite projections to equality. -/
lemma freeTarget_section_ext_of_zdisc_eval_obligation (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y) :
    x = y := by
  apply (show Function.Injective
    ((LightCondAb.freeToTopologicalFree T).hom.app ⟨S⟩) from by
      rw [← ModuleCat.mono_iff_injective]
      infer_instance)
  exact freeToTopologicalFree_section_eq_of_zdisc_eval T S h

/-- The finite projections in the chosen AsLimit presentation jointly separate sections of the free
object `ℤ[T]`, assuming separation by all integer-valued functionals. -/
lemma freeTarget_section_ext_of_finite_proj (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ k : ℕ,
      (freeProj T k).hom.app ⟨S⟩ x = (freeProj T k).hom.app ⟨S⟩ y) :
    x = y := by
  apply freeTarget_section_ext_of_zdisc_eval_obligation T S
  intro φ
  obtain ⟨k, ψ, hφ⟩ := zdisc_hom_factors_freeProj T φ
  rw [← hφ]
  change ψ.hom.app ⟨S⟩ ((freeProj T k).hom.app ⟨S⟩ x) =
    ψ.hom.app ⟨S⟩ ((freeProj T k).hom.app ⟨S⟩ y)
  rw [h k]

/-- Sections of the free object `ℤ[T]` are separated by integer-valued functions that factor through
finite quotients of `T`, reduced to finite-rank separation and joint separation of finite
projections. -/
lemma freeTarget_section_ext_of_finite_zdisc_eval (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ k : ℕ, ∀ ψ : (free ℤ).obj (T.component k).toCondensed ⟶ Zdisc,
      (freeProj T k ≫ ψ).hom.app ⟨S⟩ x = (freeProj T k ≫ ψ).hom.app ⟨S⟩ y) :
    x = y := by
  apply freeTarget_section_ext_of_finite_proj T S
  intro k
  apply finiteFree_section_ext_of_zdisc_eval (T.component k) S
  intro ψ
  exact h k ψ

/-- Sections of the free object `ℤ[T]` are separated by all locally constant integer-valued
functions on `T`, reduced to finite-stage integer-valued evaluations. -/
lemma freeTarget_section_ext_of_zdisc_eval (T S : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj ⟨S⟩)
    (h : ∀ φ : (free ℤ).obj T.toCondensed ⟶ Zdisc,
      φ.hom.app ⟨S⟩ x = φ.hom.app ⟨S⟩ y) :
    x = y := by
  apply freeTarget_section_ext_of_finite_zdisc_eval T S
  intro k ψ
  exact h (freeProj T k ≫ ψ)

/-- Endomorphisms of the free object `ℤ[T]` are determined by their composites with the free point
maps.  The proof reduces to the existing `Zdisc`-valued separation obligation. -/
lemma freeTarget_hom_ext_of_points (T : LightProfinite)
    (f g : (free ℤ).obj T.toCondensed ⟶ (free ℤ).obj T.toCondensed)
    (h : ∀ t : T, freePointMap T t ≫ f = freePointMap T t ≫ g) :
    f = g := by
  apply (freeHomEquivPoints T ((free ℤ).obj T.toCondensed)).injective
  apply freeTarget_section_ext_of_zdisc_eval T T
  intro φ
  rw [← freeHomEquivPoints_comp T f φ]
  rw [← freeHomEquivPoints_comp T g φ]
  congr 1
  apply zdisc_hom_ext_of_points
  intro t
  change (freePointMap T t ≫ f) ≫ φ = (freePointMap T t ≫ g) ≫ φ
  rw [h t]

/-- Sections of the free object `ℤ[T]` over `(ℕ∪∞) × T` are determined by all finite slices and
 the `∞` slice, assuming the standard separation of `ℤ[T]` by `ℤ`-valued functions. -/
lemma freeTarget_section_ext_of_slices (T : LightProfinite)
    (x y : ((free ℤ).obj T.toCondensed).obj.obj
      ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩)
    (hfinite : ∀ n : ℕ,
      ((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op x =
        ((free ℤ).obj T.toCondensed).obj.map (finiteTensorPoint T n).op y)
    (hinfty : ((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op x =
      ((free ℤ).obj T.toCondensed).obj.map (inftyTensorPoint T).op y) :
    x = y := by
  apply freeTarget_section_ext_of_zdisc_eval
  intro φ
  apply zdisc_section_ext_of_slices T
  · intro n
    rw [← LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op x]
    rw [← LightCondMod.hom_naturality_apply ℤ φ (finiteTensorPoint T n).op y]
    rw [hfinite]
  · rw [← LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op x]
    rw [← LightCondMod.hom_naturality_apply ℤ φ (inftyTensorPoint T).op y]
    rw [hinfty]

/-- Maps from `ℤ[(ℕ∪∞) × T]` to `ℤ[T]` are determined by all finite slices and the `∞` slice. -/
lemma freeTarget_numerator_ext_of_slices (T : LightProfinite)
    (f g : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶
      (free ℤ).obj T.toCondensed)
    (hfinite : ∀ n : ℕ,
      numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n f =
        numeratorSlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) n g)
    (hinfty : inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) f =
      inftySlice ((free ℤ).obj T.toCondensed) ((free ℤ).obj T.toCondensed) g) :
    f = g := by
  let A := (free ℤ).obj T.toCondensed
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  let y := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ g)
  have hxy : x = y := by
    apply freeTarget_section_ext_of_slices T
    · intro n
      have h := congrArg (freeHomEquivPoints T A) (hfinite n)
      rw [numeratorSlice_eq_symm_map_finite, numeratorSlice_eq_symm_map_finite] at h
      simpa [A, x, y] using h
    · have h := congrArg (freeHomEquivPoints T A) hinfty
      rw [inftySlice_eq_symm_map_infty, inftySlice_eq_symm_map_infty] at h
      simpa [A, x, y] using h
  have hmaps : (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f =
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ g := by
    apply (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).injective
    exact hxy
  apply (cancel_epi (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv).1
  exact hmaps

end ProjectiveGeneratorProof
end Solid
end LightCondensed
