import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.TopCatAdjunction
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Category.LightProfinite.AsLimit
import Mathlib.Topology.Category.Sequential
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace Sequential

/-- The topological colimit of a diagram of sequential spaces is again sequential. -/
noncomputable def colimitCoconeOfTop {J : Type} [Category J]
    (F : J ⥤ Sequential.{0}) [HasColimit (F ⋙ sequentialToTop)] : Cocone F := by
  let topF := F ⋙ sequentialToTop
  have hseq : SequentialSpace ((colimit topF : TopCat) : Type) := by
    rw [TopCat.colimit_topology topF]
    refine SequentialSpace.iSup fun j => ?_
    haveI : SequentialSpace ((topF.obj j : TopCat) : Type) := by
      change SequentialSpace ((F.obj j).toTop : Type)
      infer_instance
    exact SequentialSpace.coinduced (colimit.ι topF j)
  refine { pt := { toTop := colimit topF, is_sequential := hseq }, ι := ?_ }
  refine { app := fun j => InducedCategory.homMk (colimit.ι topF j), naturality := ?_ }
  intro i j f
  ext x
  exact ConcreteCategory.congr_hom ((colimit.cocone topF).ι.naturality f) x

/-- The cocone obtained from the topological colimit is colimiting in sequential spaces. -/
noncomputable def colimitCoconeOfTop_isColimit {J : Type} [Category J]
    (F : J ⥤ Sequential.{0}) [HasColimit (F ⋙ sequentialToTop)] :
    IsColimit (colimitCoconeOfTop F) := by
  refine IsColimit.ofFaithful sequentialToTop (colimit.isColimit (F ⋙ sequentialToTop)) ?_ ?_
  · intro s
    exact sequentialToTop.preimage (X := (colimitCoconeOfTop F).pt) (Y := s.pt)
      (colimit.desc (F ⋙ sequentialToTop) (sequentialToTop.mapCocone s))
  · intro s
    change sequentialToTop.map
        (sequentialToTop.preimage (X := (colimitCoconeOfTop F).pt) (Y := s.pt)
          (colimit.desc (F ⋙ sequentialToTop) (sequentialToTop.mapCocone s))) =
      colimit.desc (F ⋙ sequentialToTop) (sequentialToTop.mapCocone s)
    rw [Functor.map_preimage]

/-- The inclusion of sequential spaces into topological spaces preserves colimits. -/
noncomputable instance preservesColimit_sequentialToTop {J : Type} [Category J]
    (F : J ⥤ Sequential.{0}) [HasColimit (F ⋙ sequentialToTop)] :
    PreservesColimit F sequentialToTop :=
  preservesColimit_of_preserves_colimit_cocone (colimitCoconeOfTop_isColimit F) (by
    exact IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ sequentialToTop))
      (Cocone.ext (Iso.refl _) (by intro j; rfl)))

/-- The concrete forgetful functor from sequential spaces is the same as first forgetting to
`TopCat` and then to types. -/
noncomputable def forgetIso : (forget Sequential.{0}) ≅ (sequentialToTop ⋙ forget TopCat) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)

noncomputable instance preservesColimit_forget {J : Type} [Category J]
    (F : J ⥤ Sequential.{0}) [HasColimit (F ⋙ sequentialToTop)] :
    PreservesColimit F (forget Sequential) :=
  preservesColimit_of_natIso F forgetIso.symm

end Sequential

namespace LightCondSet

/-- If a light condensed set is represented by its topological realization, then a morphism out of
it is sectionwise injective as soon as it is injective on point-valued sections. -/
lemma injective_app_of_topCatAdjunctionUnit_iso_and_injective_point {X Y : LightCondSet.{0}}
    (f : X ⟶ Y)
    [IsIso (topCatAdjunctionUnit X)]
    (hpt : Function.Injective (f.hom.app ⟨LightProfinite.of PUnit⟩))
    (S : LightProfinite) :
    Function.Injective (f.hom.app ⟨S⟩) := by
  intro x y hxy
  let η := topCatAdjunctionUnit X
  have hη : η.hom.app ⟨S⟩ x = η.hom.app ⟨S⟩ y := by
    letI : TopologicalSpace ((X.toTopCat : TopCat) : Type) := X.toTopCat.str
    change (show C(↑S.toTop, ((X.toTopCat : TopCat) : Type)) from η.hom.app ⟨S⟩ x) =
      (show C(↑S.toTop, ((X.toTopCat : TopCat) : Type)) from η.hom.app ⟨S⟩ y)
    apply ContinuousMap.ext
    intro s
    have hηx : ((show C(↑S.toTop, ((X.toTopCat : TopCat) : Type)) from
        η.hom.app ⟨S⟩ x) s) =
        X.obj.map ((LightProfinite.of PUnit).const s).op x := by
      dsimp [η]
      rw [topCatAdjunctionUnit_hom_app]
      rfl
    have hηy : ((show C(↑S.toTop, ((X.toTopCat : TopCat) : Type)) from
        η.hom.app ⟨S⟩ y) s) =
        X.obj.map ((LightProfinite.of PUnit).const s).op y := by
      dsimp [η]
      rw [topCatAdjunctionUnit_hom_app]
      rfl
    rw [hηx, hηy]
    apply hpt
    rw [NatTrans.naturality_apply f.hom ((LightProfinite.of PUnit).const s).op x]
    rw [NatTrans.naturality_apply f.hom ((LightProfinite.of PUnit).const s).op y]
    exact congrArg (fun z => Y.obj.map ((LightProfinite.of PUnit).const s).op z) hxy
  have hη' := congrArg (fun z => (asIso η).inv.hom.app ⟨S⟩ z) hη
  change (η ≫ (asIso η).inv).hom.app ⟨S⟩ x =
    (η ≫ (asIso η).inv).hom.app ⟨S⟩ y at hη'
  simpa using hη'

end LightCondSet

namespace LightProfinite

namespace FreeImage

/-- Total variation of a finite signed measure on a finite set. -/
def totalVariation {α : Type*} (a : α →₀ ℤ) : ℤ :=
  a.sum fun _ n => |n|

lemma totalVariation_eq_sum_fintype {α : Type*} [Fintype α] (a : α →₀ ℤ) :
    totalVariation a = ∑ i, |a i| := by
  rw [totalVariation, Finsupp.sum_fintype]
  intro i
  simp

lemma totalVariation_nonneg {α : Type*} (a : α →₀ ℤ) : 0 ≤ totalVariation a := by
  dsimp [totalVariation, Finsupp.sum]
  positivity

lemma abs_apply_le_totalVariation {α : Type*} (a : α →₀ ℤ) (i : α) :
    |a i| ≤ totalVariation a := by
  by_cases hi : i ∈ a.support
  · dsimp [totalVariation, Finsupp.sum]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (a j)) hi
  · have hzero : a i = 0 := by
      simpa [Finsupp.mem_support_iff] using hi
    simp [hzero, totalVariation_nonneg a]

lemma apply_mem_Icc_of_totalVariation_le {α : Type*} (a : α →₀ ℤ) {c : ℤ}
    (_hc : 0 ≤ c) (ha : totalVariation a ≤ c) (i : α) :
    a i ∈ Set.Icc (-c) c := by
  have habs : |a i| ≤ c := le_trans (abs_apply_le_totalVariation a i) ha
  exact abs_le.mp habs

lemma abs_mapDomain_apply_le_sum_filter {α β : Type*} [DecidableEq β]
    (f : α → β) (a : α →₀ ℤ) (b : β) :
    |(Finsupp.mapDomain f a) b| ≤ ∑ i ∈ a.support with f i = b, |a i| := by
  classical
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a0, rfl⟩ := hb
    rw [Finsupp.mapDomain_apply_eq_sum]
    exact Finset.abs_sum_le_sum_abs (fun i => a i) (a.support.filter fun i => f i = f a0)
  · rw [Finsupp.mapDomain_notin_range a b hb]
    positivity

/-- Pushing a finite signed measure forward cannot increase total variation. -/
lemma totalVariation_mapDomain_le {α β : Type*} [Fintype β] [DecidableEq β]
    (f : α → β) (a : α →₀ ℤ) :
    totalVariation (Finsupp.mapDomain f a) ≤ totalVariation a := by
  classical
  calc
    totalVariation (Finsupp.mapDomain f a)
        = ∑ b : β, |(Finsupp.mapDomain f a) b| :=
          totalVariation_eq_sum_fintype _
    _ ≤ ∑ b : β, ∑ i ∈ a.support with f i = b, |a i| := by
          exact Finset.sum_le_sum fun b _ => abs_mapDomain_apply_le_sum_filter f a b
    _ = ∑ i ∈ a.support, |a i| := by
          rw [Finset.sum_fiberwise]
    _ = totalVariation a := by
          rw [totalVariation, Finsupp.sum]

/-- The bounded finite-stage signed measures on a finite set. -/
def set (Si : FintypeCat.{0}) (c : ℤ) : Set (Si →₀ ℤ) :=
  {a | totalVariation a ≤ c }

instance (Si : FintypeCat.{0}) (c : ℤ) : Fintype (set Si c) := by
  classical
  by_cases hc : 0 ≤ c
  · letI : Fintype Si := FintypeCat.fintype
    letI : Fintype (Set.Icc (-c) c) := Set.Finite.fintype (Set.finite_Icc (-c) c)
    let f : set Si c → (Si → Set.Icc (-c) c) := fun a i =>
      ⟨a.1 i, apply_mem_Icc_of_totalVariation_le a.1 hc a.2 i⟩
    exact Fintype.ofInjective f (by
      intro a b h
      ext i
      exact congrArg Subtype.val (congrFun h i))
  · have hempty : IsEmpty (set Si c) := by
      refine ⟨fun a => ?_⟩
      exact hc (le_trans (totalVariation_nonneg a.1) a.2)
    exact Fintype.ofFinite (set Si c)

def component (Si : FintypeCat.{0}) (c : ℤ) : LightProfinite :=
  FintypeCat.toLightProfinite.obj (FintypeCat.of (set Si c))

/-- Push forward bounded finite-stage signed measures along a finite-set map. -/
def fintypeMap (c : ℤ) {Si Sj : FintypeCat.{0}} (f : Si ⟶ Sj) :
    FintypeCat.of (set Si c) ⟶ FintypeCat.of (set Sj c) := by
  classical
  letI : Fintype Sj := FintypeCat.fintype
  exact ConcreteCategory.ofHom (TypeCat.Fun.mk fun a =>
    ⟨Finsupp.mapDomain f a.1, le_trans (totalVariation_mapDomain_le f a.1) a.2⟩)

/-- The finite-stage bounded-measure functor before adding the discrete topology. -/
def fintypeFunctor (c : ℤ) : FintypeCat ⥤ FintypeCat where
  obj Si := FintypeCat.of (set Si c)
  map {Si Sj} f := fintypeMap c f
  map_id := by
    intro Si
    ext a i
    change (Finsupp.mapDomain id (↑a : Si →₀ ℤ)) i = (↑a : Si →₀ ℤ) i
    rw [Finsupp.mapDomain_id]
  map_comp := by
    intro Si Sj Sk f g
    ext a i
    change (Finsupp.mapDomain ((⇑(ConcreteCategory.hom g)) ∘ (⇑(ConcreteCategory.hom f)))
        (↑a : Si →₀ ℤ)) i =
      (Finsupp.mapDomain (⇑(ConcreteCategory.hom g))
        (Finsupp.mapDomain (⇑(ConcreteCategory.hom f)) (↑a : Si →₀ ℤ))) i
    rw [Finsupp.mapDomain_comp]

/-- Bounded finite-stage signed measures as a light profinite functor. -/
def functor (c : ℤ) : FintypeCat ⥤ LightProfinite :=
  fintypeFunctor c ⋙ FintypeCat.toLightProfinite

def profiniteComponent (S : LightProfinite.{0}) (c : ℤ) : LightProfinite :=
  limit (S.fintypeDiagram ⋙ functor c)

/-- Inclusion of bounded finite-stage measures when the bound increases. -/
def boundInclusion (Si : FintypeCat.{0}) {c d : ℤ} (hcd : c ≤ d) :
    FintypeCat.of (set Si c) ⟶ FintypeCat.of (set Si d) :=
  ConcreteCategory.ofHom (TypeCat.Fun.mk fun a => ⟨a.1, le_trans a.2 hcd⟩)

/-- The natural inclusion of bounded-measure functors for increasing bounds. -/
def boundInclusionNat {c d : ℤ} (hcd : c ≤ d) :
    fintypeFunctor c ⟶ fintypeFunctor d where
  app Si := boundInclusion Si hcd
  naturality := by
    intro Si Sj f
    ext a
    rfl

/-- The natural inclusion after adding the discrete light profinite topology. -/
def functorBoundInclusion {c d : ℤ} (hcd : c ≤ d) :
    functor c ⟶ functor d :=
  Functor.whiskerRight (boundInclusionNat hcd) FintypeCat.toLightProfinite

lemma boundInclusionNat_refl (c : ℤ) :
    boundInclusionNat (le_refl c) = 𝟙 (fintypeFunctor c) := by
  ext Si a
  rfl

lemma boundInclusionNat_comp {c d e : ℤ} (hcd : c ≤ d) (hde : d ≤ e) :
    boundInclusionNat (le_trans hcd hde) =
      boundInclusionNat hcd ≫ boundInclusionNat hde := by
  ext Si a
  rfl

lemma functorBoundInclusion_refl (c : ℤ) :
    functorBoundInclusion (le_refl c) = 𝟙 (functor c) := by
  dsimp [functorBoundInclusion, functor]
  rw [boundInclusionNat_refl]
  rfl

lemma functorBoundInclusion_comp {c d e : ℤ} (hcd : c ≤ d) (hde : d ≤ e) :
    functorBoundInclusion (le_trans hcd hde) =
      functorBoundInclusion hcd ≫ functorBoundInclusion hde := by
  dsimp [functorBoundInclusion, functor]
  rw [boundInclusionNat_comp hcd hde]
  rfl

/-- The map between profinite bounded-measure components induced by increasing the bound. -/
noncomputable def profiniteComponentMap (S : LightProfinite.{0}) {c d : ℤ} (hcd : c ≤ d) :
    profiniteComponent S c ⟶ profiniteComponent S d :=
  _root_.CategoryTheory.Limits.lim.map
    (Functor.whiskerLeft S.fintypeDiagram (functorBoundInclusion hcd))

lemma profiniteComponentMap_congr (S : LightProfinite.{0}) {c d : ℤ} (h₁ h₂ : c ≤ d) :
    profiniteComponentMap S h₁ = profiniteComponentMap S h₂ := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  cases h
  rfl

lemma profiniteComponentMap_id (S : LightProfinite.{0}) (c : ℤ) :
    profiniteComponentMap S (le_refl c) = 𝟙 (profiniteComponent S c) := by
  have hα : Functor.whiskerLeft S.fintypeDiagram (functorBoundInclusion (le_refl c)) =
      𝟙 (S.fintypeDiagram ⋙ functor c) := by
    rw [functorBoundInclusion_refl]
    rfl
  dsimp [profiniteComponentMap]
  rw [hα]
  exact _root_.CategoryTheory.Limits.lim.map_id (S.fintypeDiagram ⋙ functor c)

lemma profiniteComponentMap_comp (S : LightProfinite.{0}) {c d e : ℤ}
    (hcd : c ≤ d) (hde : d ≤ e) :
    profiniteComponentMap S (le_trans hcd hde) =
      profiniteComponentMap S hcd ≫ profiniteComponentMap S hde := by
  let α := Functor.whiskerLeft S.fintypeDiagram (functorBoundInclusion hcd)
  let β := Functor.whiskerLeft S.fintypeDiagram (functorBoundInclusion hde)
  have hαβ : Functor.whiskerLeft S.fintypeDiagram
        (functorBoundInclusion (le_trans hcd hde)) = α ≫ β := by
    dsimp [α, β]
    rw [functorBoundInclusion_comp hcd hde]
    rfl
  dsimp [profiniteComponentMap]
  rw [hαβ]
  exact _root_.CategoryTheory.Limits.lim.map_comp α β

/-- A morphism in the preorder category `ℕ+` gives the corresponding integer inequality. -/
theorem pnatHomLeInt {c d : ℕ+} (h : c ⟶ d) : (c : ℤ) ≤ (d : ℤ) := by
  have hnat : (c : ℕ) ≤ (d : ℕ) := leOfHom h
  exact_mod_cast hnat

def _root_.lightProfiniteToSequential : LightProfinite ⥤ Sequential where
  obj X := Sequential.of X
  map {X Y} f :=
    ConcreteCategory.ofHom (X := Sequential.of X) (Y := Sequential.of Y)
      (⟨(f : X → Y), by continuity⟩ : C(↑(Sequential.of X).toTop, ↑(Sequential.of Y).toTop))
  map_id := by
    intro X
    ext x
    simp
  map_comp := by
    intro X Y Z f g
    ext x
    simp

-- This functor should probably be defined as a right Kan extension of the analogous functor to
-- `FintypeCat`, similarly to `Condensed.profiniteSolid`, defined in `Mathlib.Condensed.Solid`.
-- But it will be isomorphic objectwise to `profiniteComponent S c`.
def seqFunctor (S : LightProfinite.{0}) : ℕ+ ⥤ LightProfinite where
  obj c := profiniteComponent S c
  map {c d} h := profiniteComponentMap S (pnatHomLeInt h)
  map_id := by
    intro c
    trans profiniteComponentMap S (le_refl (c : ℤ))
    · apply profiniteComponentMap_congr
    · exact profiniteComponentMap_id S c
  map_comp := by
    intro c d e f g
    trans profiniteComponentMap S (le_trans (pnatHomLeInt f) (pnatHomLeInt g))
    · apply profiniteComponentMap_congr
    · exact profiniteComponentMap_comp S (pnatHomLeInt f) (pnatHomLeInt g)

/-- The restricted topological-realization adjunction makes sequential spaces a reflective
subcategory of light condensed sets. -/
noncomputable instance : sequentialToLightCondSet.{0}.Faithful :=
  fullyFaithfulSequentialToLightCondSet.faithful

noncomputable instance : sequentialToLightCondSet.{0}.Full :=
  fullyFaithfulSequentialToLightCondSet.full

noncomputable instance : Reflective sequentialToLightCondSet.{0} where
  L := lightCondSetToSequential
  adj := sequentialAdjunction

instance : HasCountableColimits Sequential.{0} where
  out J _ _ := by
    haveI : HasColimitsOfShape J LightCondSet.{0} := inferInstance
    exact hasColimitsOfShape_of_reflective (J := J) (C := LightCondSet.{0})
      (D := Sequential.{0}) sequentialToLightCondSet.{0}

instance : CountableCategory ℕ+ where

def sequential (S : LightProfinite.{0}) : Sequential :=
  colimit (seqFunctor S ⋙ lightProfiniteToSequential)

/-- The discrete sequential space of integers, used as the target for finite-measure evaluations. -/
abbrev discreteIntSeq : Sequential := Sequential.of ℤ

/-- Evaluate a bounded finite-stage signed measure against an integer-valued function on the finite
stage. -/
noncomputable def finiteStageEval (Si : FintypeCat.{0}) (c : ℤ) (g : Si → ℤ) :
    component Si c → ℤ :=
  fun a => (a : set Si c).1.sum fun i n => n * g i

@[simp]
lemma finiteStageEval_boundInclusion (Si : FintypeCat.{0}) {c d : ℤ} (hcd : c ≤ d)
    (g : Si → ℤ) (a : set Si c) :
    finiteStageEval Si d g (boundInclusion Si hcd a) = finiteStageEval Si c g a := by
  rfl

@[simp]
lemma finiteStageEval_fintypeMap (c : ℤ) {Si Sj : FintypeCat.{0}} (f : Si ⟶ Sj)
    (g : Sj → ℤ) (a : set Si c) :
    finiteStageEval Sj c g (fintypeMap c f a) = finiteStageEval Si c (fun i => g (f i)) a := by
  classical
  change (Finsupp.mapDomain (fun i => f i) (a.1 : Si →₀ ℤ)).sum (fun i n => n * g i) =
    (a.1 : Si →₀ ℤ).sum (fun i n => n * g (f i))
  rw [Finsupp.sum_mapDomain_index]
  · intro x
    simp
  · intro b m₁ m₂
    ring

/-- The Dirac measure at a point of a finite stage, with total variation bounded by `1`. -/
noncomputable def diracFintype (Si : FintypeCat.{0}) (i : Si) : set Si (1 : ℤ) := by
  classical
  refine ⟨Finsupp.single i (1 : ℤ), ?_⟩
  change (Finsupp.single i (1 : ℤ)).sum (fun _ n => |n|) ≤ 1
  simp

@[simp]
lemma finiteStageEval_diracFintype (Si : FintypeCat.{0}) (g : Si → ℤ) (i : Si) :
    finiteStageEval Si (1 : ℤ) g (diracFintype Si i) = g i := by
  classical
  dsimp [finiteStageEval, diracFintype]
  simp

@[simp]
lemma fintypeMap_diracFintype {Si Sj : FintypeCat.{0}} (f : Si ⟶ Sj) (i : Si) :
    fintypeMap (1 : ℤ) f (diracFintype Si i) = diracFintype Sj (f i) := by
  classical
  ext j
  dsimp [fintypeMap, diracFintype]
  simp [Finsupp.mapDomain_single]

/-- Bounded finite-stage signed measures are separated by their evaluations against all
integer-valued functions on the finite stage. -/
lemma finiteStageEval_ext (Si : FintypeCat.{0}) (c : ℤ) {a b : set Si c}
    (h : ∀ g : Si → ℤ, finiteStageEval Si c g a = finiteStageEval Si c g b) : a = b := by
  classical
  ext i
  let g : Si → ℤ := fun j => if j = i then 1 else 0
  have hg := h g
  have ha : finiteStageEval Si c g a = a.1 i := by
    dsimp [finiteStageEval, g]
    rw [Finsupp.sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      have hzero : a.1 i = 0 := by
        simpa [Finsupp.mem_support_iff] using hi
      simp [hzero]
  have hb : finiteStageEval Si c g b = b.1 i := by
    dsimp [finiteStageEval, g]
    rw [Finsupp.sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      have hzero : b.1 i = 0 := by
        simpa [Finsupp.mem_support_iff] using hi
      simp [hzero]
  simpa [ha, hb] using hg

/-- Evaluation of a bounded profinite component against a function that factors through a finite
stage `k`. -/
noncomputable def profiniteComponentEval (S : LightProfinite.{0}) (c : ℤ) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) :
    lightProfiniteToSequential.obj (profiniteComponent S c) ⟶ discreteIntSeq := by
  let πk : profiniteComponent S c ⟶ component (S.fintypeDiagram.obj ⟨k⟩) c :=
    limit.π (S.fintypeDiagram ⋙ functor c) ⟨k⟩
  let e : component (S.fintypeDiagram.obj ⟨k⟩) c → ℤ := finiteStageEval _ c g
  have he : Continuous e := by
    dsimp [e, finiteStageEval, FreeImage.component, FintypeCat.toLightProfinite]
    fun_prop
  refine ConcreteCategory.ofHom (X := lightProfiniteToSequential.obj (profiniteComponent S c))
    (Y := discreteIntSeq) ?_
  refine (⟨fun x => e (πk x), ?_⟩ :
    C(↑(lightProfiniteToSequential.obj (profiniteComponent S c)).toTop, ↑discreteIntSeq.toTop))
  exact he.comp πk.hom.hom.continuous

/-- The bounded-component evaluation maps are compatible with increasing the bound. -/
lemma profiniteComponentEval_bound (S : LightProfinite.{0}) {c d : ℤ} (hcd : c ≤ d) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) :
    lightProfiniteToSequential.map (profiniteComponentMap S hcd) ≫
      profiniteComponentEval S d k g = profiniteComponentEval S c k g := by
  ext x
  let α := Functor.whiskerLeft S.fintypeDiagram (functorBoundInclusion hcd)
  have hπ : profiniteComponentMap S hcd ≫ limit.π (S.fintypeDiagram ⋙ functor d) ⟨k⟩ =
      limit.π (S.fintypeDiagram ⋙ functor c) ⟨k⟩ ≫ α.app ⟨k⟩ := by
    dsimp [profiniteComponentMap]
    rw [lim_map]
    exact limMap_π α ⟨k⟩
  have hx : ((profiniteComponentMap S hcd ≫ limit.π (S.fintypeDiagram ⋙ functor d) ⟨k⟩) x) =
      (α.app ⟨k⟩ ((limit.π (S.fintypeDiagram ⋙ functor c) ⟨k⟩) x)) := by
    have hxraw := congrArg
      (fun m : profiniteComponent S c ⟶ (S.fintypeDiagram ⋙ functor d).obj ⟨k⟩ => m x) hπ
    change ((profiniteComponentMap S hcd ≫ limit.π (S.fintypeDiagram ⋙ functor d) ⟨k⟩) x) =
      ((limit.π (S.fintypeDiagram ⋙ functor c) ⟨k⟩ ≫ α.app ⟨k⟩) x) at hxraw
    simpa only [CategoryTheory.comp_apply] using hxraw
  dsimp [profiniteComponentEval]
  change finiteStageEval (S.fintypeDiagram.obj ⟨k⟩) d g
      ((profiniteComponentMap S hcd ≫ limit.π (S.fintypeDiagram ⋙ functor d) ⟨k⟩) x) =
    finiteStageEval (S.fintypeDiagram.obj ⟨k⟩) c g
      ((limit.π (S.fintypeDiagram ⋙ functor c) ⟨k⟩) x)
  rw [hx]
  rfl

/-- Points in a fixed bounded profinite component are separated by all finite-stage evaluations. -/
lemma profiniteComponentEval_ext (S : LightProfinite.{0}) (c : ℤ)
    {x y : profiniteComponent S c}
    (h : ∀ k : ℕ, ∀ g : S.fintypeDiagram.obj ⟨k⟩ → ℤ,
      profiniteComponentEval S c k g x = profiniteComponentEval S c k g y) :
    x = y := by
  apply Concrete.limit_ext (S.fintypeDiagram ⋙ functor c) x y
  intro k
  apply finiteStageEval_ext (S.fintypeDiagram.obj k) c
  intro g
  have hg := h k.unop g
  dsimp [profiniteComponentEval] at hg
  exact hg

/-- Maps into a fixed bounded profinite component are separated by finite-stage evaluations. -/
lemma profiniteComponentEval_hom_ext (S : LightProfinite.{0}) (c : ℤ) {X : Sequential}
    {f g : X ⟶ lightProfiniteToSequential.obj (profiniteComponent S c)}
    (h : ∀ k : ℕ, ∀ e : S.fintypeDiagram.obj ⟨k⟩ → ℤ,
      f ≫ profiniteComponentEval S c k e = g ≫ profiniteComponentEval S c k e) :
    f = g := by
  ext x
  apply profiniteComponentEval_ext S c
  intro k e
  exact congrArg (fun m : X ⟶ discreteIntSeq => m x) (h k e)

/-- Sections of a fixed bounded profinite component are separated by finite-stage evaluations. -/
lemma profiniteComponent_section_ext_of_eval (T U : LightProfinite.{0}) (c : ℤ)
    {x y : (sequentialToLightCondSet.obj
      (lightProfiniteToSequential.obj (profiniteComponent T c))).obj.obj ⟨U⟩}
    (h : ∀ k : ℕ, ∀ e : T.fintypeDiagram.obj ⟨k⟩ → ℤ,
      (sequentialToLightCondSet.map (profiniteComponentEval T c k e)).hom.app ⟨U⟩ x =
        (sequentialToLightCondSet.map (profiniteComponentEval T c k e)).hom.app ⟨U⟩ y) :
    x = y := by
  apply ContinuousMap.ext
  intro u
  apply profiniteComponentEval_ext T c
  intro k e
  have hk := congrArg (fun f : C(↑U.toTop, ↑discreteIntSeq.toTop) => f u) (h k e)
  change ((profiniteComponentEval T c k e)
      ((show C(↑U.toTop, ↑(lightProfiniteToSequential.obj (profiniteComponent T c)).toTop) from x).toFun u)) =
    ((profiniteComponentEval T c k e)
      ((show C(↑U.toTop, ↑(lightProfiniteToSequential.obj (profiniteComponent T c)).toTop) from y).toFun u)) at hk
  exact hk

/-- The compatible cone of finite-stage Dirac measures over all finite quotients of `S`. -/
noncomputable def diracCone (S : LightProfinite.{0}) :
    Cone (S.fintypeDiagram ⋙ functor (1 : ℤ)) where
  pt := S
  π := {
    app k := by
      refine ConcreteCategory.ofHom ?_
      refine (⟨fun s => diracFintype (S.fintypeDiagram.obj k) (S.proj k.unop s), ?_⟩ :
        C(↑S.toTop, ↑(component (S.fintypeDiagram.obj k) (1 : ℤ)).toTop))
      dsimp [component, FintypeCat.toLightProfinite]
      fun_prop
    naturality := by
      intro i j h
      ext s
      simp only [Functor.const_obj_map]
      change diracFintype (S.fintypeDiagram.obj j) (S.proj j.unop s) =
        (fintypeMap (1 : ℤ) (S.fintypeDiagram.map h)
          (diracFintype (S.fintypeDiagram.obj i) (S.proj i.unop s)))
      rw [fintypeMap_diracFintype]
      have hw := congrArg (fun f : S ⟶ S.diagram.obj j => f s) (S.asLimitCone.w h)
      exact (congrArg (fun x => diracFintype (S.fintypeDiagram.obj j) x) hw).symm }

/-- The continuous map sending a point of `S` to its Dirac measure in the bound-`1` profinite
component. -/
noncomputable def diracComponent (S : LightProfinite.{0}) : S ⟶ profiniteComponent S (1 : ℤ) :=
  limit.lift (S.fintypeDiagram ⋙ functor (1 : ℤ)) (diracCone S)

/-- The same Dirac component, typed as the `1`st object of the bounded-measure sequence. -/
noncomputable def diracComponentOne (S : LightProfinite.{0}) : S ⟶ (seqFunctor S).obj (1 : ℕ+) :=
  diracComponent S

@[simp]
lemma diracComponent_π (S : LightProfinite.{0}) (k : ℕ) :
    diracComponent S ≫ limit.π (S.fintypeDiagram ⋙ functor (1 : ℤ)) ⟨k⟩ =
      (diracCone S).π.app ⟨k⟩ := by
  exact limit.lift_π _ _

@[simp]
lemma diracComponent_apply_π (S : LightProfinite.{0}) (k : ℕ) (s : S) :
    (limit.π (S.fintypeDiagram ⋙ functor (1 : ℤ)) ⟨k⟩) (diracComponent S s) =
      diracFintype (S.fintypeDiagram.obj ⟨k⟩) (S.proj k s) := by
  change ((diracComponent S ≫ limit.π (S.fintypeDiagram ⋙ functor (1 : ℤ)) ⟨k⟩) s) =
    diracFintype (S.fintypeDiagram.obj ⟨k⟩) (S.proj k s)
  rw [diracComponent_π]
  rfl

@[simp]
lemma profiniteComponentEval_diracComponent (S : LightProfinite.{0}) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) (s : S) :
    profiniteComponentEval S (1 : ℤ) k g (diracComponent S s) = g (S.proj k s) := by
  dsimp [profiniteComponentEval]
  change finiteStageEval (S.fintypeDiagram.obj ⟨k⟩) (1 : ℤ) g
      ((limit.π (S.fintypeDiagram ⋙ functor (1 : ℤ)) ⟨k⟩) (diracComponent S s)) =
    g (S.proj k s)
  rw [diracComponent_apply_π]
  simp

/-- The map from `S` into the full sequential finite-measure model sending a point to its Dirac
measure. -/
noncomputable def diracSequential (S : LightProfinite.{0}) :
    lightProfiniteToSequential.obj S ⟶ sequential S :=
  lightProfiniteToSequential.map (diracComponentOne S) ≫
    colimit.ι (seqFunctor S ⋙ lightProfiniteToSequential) (1 : ℕ+)

/-- The cocone induced by evaluating the bounded pieces against a finite-stage integer-valued
function. -/
noncomputable def sequentialEvalCoconeOfFactor (S : LightProfinite.{0}) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) :
    Cocone (seqFunctor S ⋙ lightProfiniteToSequential) where
  pt := discreteIntSeq
  ι := {
    app c := profiniteComponentEval S c k g
    naturality := by
      intro c d h
      exact profiniteComponentEval_bound S (pnatHomLeInt h) k g }

/-- Evaluation of the sequential finite-measure model against an integer-valued function that
factors through a finite stage. -/
noncomputable def sequentialEvalOfFactor (S : LightProfinite.{0}) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) :
    sequential S ⟶ discreteIntSeq :=
  colimit.desc (seqFunctor S ⋙ lightProfiniteToSequential) (sequentialEvalCoconeOfFactor S k g)

@[simp]
lemma colimit_ι_sequentialEvalOfFactor (S : LightProfinite.{0}) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) (c : ℕ+) :
    colimit.ι (seqFunctor S ⋙ lightProfiniteToSequential) c ≫ sequentialEvalOfFactor S k g =
      profiniteComponentEval S c k g := by
  exact colimit.ι_desc _ c

@[simp]
lemma diracSequential_eval_apply (S : LightProfinite.{0}) (k : ℕ)
    (g : S.fintypeDiagram.obj ⟨k⟩ → ℤ) (s : S) :
    (diracSequential S ≫ sequentialEvalOfFactor S k g) s = g (S.proj k s) := by
  have hm : diracSequential S ≫ sequentialEvalOfFactor S k g =
      lightProfiniteToSequential.map (diracComponentOne S) ≫
        profiniteComponentEval S ((1 : ℕ+) : ℤ) k g := by
    dsimp [diracSequential]
    erw [Category.assoc, colimit_ι_sequentialEvalOfFactor]
    rfl
  have hs := congrArg (fun m : lightProfiniteToSequential.obj S ⟶ discreteIntSeq => m s) hm
  dsimp [diracComponentOne] at hs
  change (diracSequential S ≫ sequentialEvalOfFactor S k g) s =
    profiniteComponentEval S (1 : ℤ) k g (diracComponent S s) at hs
  exact hs.trans (profiniteComponentEval_diracComponent S k g s)

/-- Points of the sequential finite-measure model are separated by finite-stage evaluations. -/
lemma sequentialEvalOfFactor_ext (S : LightProfinite.{0})
    {x y : sequential S}
    (h : ∀ k : ℕ, ∀ g : S.fintypeDiagram.obj ⟨k⟩ → ℤ,
      sequentialEvalOfFactor S k g x = sequentialEvalOfFactor S k g y) :
    x = y := by
  let F := seqFunctor S ⋙ lightProfiniteToSequential
  obtain ⟨c, xc, rfl⟩ := Concrete.colimit_exists_rep F x
  obtain ⟨d, yd, rfl⟩ := Concrete.colimit_exists_rep F y
  apply Concrete.colimit_rep_eq_of_exists F xc yd
  let e := IsFiltered.max c d
  let fc : c ⟶ e := IsFiltered.leftToMax c d
  let fd : d ⟶ e := IsFiltered.rightToMax c d
  refine ⟨e, fc, fd, ?_⟩
  apply profiniteComponentEval_ext S (e : ℤ)
  intro k g
  have hxy := h k g
  change (colimit.ι F c ≫ sequentialEvalOfFactor S k g) xc =
    (colimit.ι F d ≫ sequentialEvalOfFactor S k g) yd at hxy
  rw [colimit_ι_sequentialEvalOfFactor, colimit_ι_sequentialEvalOfFactor] at hxy
  have hc := congrArg
    (fun m : lightProfiniteToSequential.obj (profiniteComponent S c) ⟶ discreteIntSeq => m xc)
    (profiniteComponentEval_bound S (pnatHomLeInt fc) k g)
  have hd := congrArg
    (fun m : lightProfiniteToSequential.obj (profiniteComponent S d) ⟶ discreteIntSeq => m yd)
    (profiniteComponentEval_bound S (pnatHomLeInt fd) k g)
  change profiniteComponentEval S (e : ℤ) k g ((F.map fc) xc) =
    profiniteComponentEval S (c : ℤ) k g xc at hc
  change profiniteComponentEval S (e : ℤ) k g ((F.map fd) yd) =
    profiniteComponentEval S (d : ℤ) k g yd at hd
  rw [hc, hd]
  exact hxy

/-- Sections of the sequential finite-measure model are separated by finite-stage evaluations. -/
lemma sequential_section_ext_of_eval (T U : LightProfinite.{0})
    {x y : (sequentialToLightCondSet.obj (sequential T)).obj.obj ⟨U⟩}
    (h : ∀ k : ℕ, ∀ g : T.fintypeDiagram.obj ⟨k⟩ → ℤ,
      (sequentialToLightCondSet.map (sequentialEvalOfFactor T k g)).hom.app ⟨U⟩ x =
        (sequentialToLightCondSet.map (sequentialEvalOfFactor T k g)).hom.app ⟨U⟩ y) :
    x = y := by
  apply ContinuousMap.ext
  intro u
  apply sequentialEvalOfFactor_ext T
  intro k g
  have hk := congrArg (fun f : C(↑U.toTop, ↑discreteIntSeq.toTop) => f u) (h k g)
  change (sequentialEvalOfFactor T k g)
      ((show C(↑U.toTop, ↑(sequential T).toTop) from x) u) =
    (sequentialEvalOfFactor T k g)
      ((show C(↑U.toTop, ↑(sequential T).toTop) from y) u) at hk
  exact hk

end FreeImage

/-- The finite quotient projections of a light profinite space jointly separate points. -/
lemma eq_of_forall_proj_eq (S : LightProfinite.{0}) {x y : S}
    (h : ∀ n : ℕ, S.proj n x = S.proj n y) : x = y := by
  let X : LightProfinite.{0} := LightProfinite.of PUnit
  let fx : X ⟶ S := X.const x
  let fy : X ⟶ S := X.const y
  have hfg : fx = fy := by
    apply S.asLimit.hom_ext
    intro n
    ext p
    change S.proj n.unop (fx p) = S.proj n.unop (fy p)
    have hx : fx p = x := rfl
    have hy : fy p = y := rfl
    rw [hx, hy]
    exact h n.unop
  have hp := ConcreteCategory.congr_hom hfg PUnit.unit
  have hx : fx PUnit.unit = x := rfl
  have hy : fy PUnit.unit = y := rfl
  simpa [hx, hy] using hp

/-- Distinct points of a light profinite space are separated by some finite quotient projection. -/
lemma exists_proj_ne (S : LightProfinite.{0}) {x y : S} (hxy : x ≠ y) :
    ∃ n : ℕ, S.proj n x ≠ S.proj n y := by
  by_contra h
  apply hxy
  apply eq_of_forall_proj_eq S
  intro n
  by_contra hn
  exact h ⟨n, hn⟩

/-- Distinct maps into a light profinite space are separated after postcomposition with some finite
quotient projection. -/
lemma exists_proj_comp_ne_of_ne {U S : LightProfinite.{0}} {g h : U ⟶ S} (hgh : g ≠ h) :
    ∃ n : ℕ, g ≫ S.proj n ≠ h ≫ S.proj n := by
  obtain ⟨u, hu⟩ : ∃ u : U, g u ≠ h u := by
    by_contra H
    apply hgh
    ext u
    by_contra hu
    exact H ⟨u, hu⟩
  obtain ⟨n, hn⟩ := exists_proj_ne S hu
  refine ⟨n, ?_⟩
  intro H
  apply hn
  exact ConcreteCategory.congr_hom H u

/-- Separation by a finite quotient persists after passing to any later quotient. -/
lemma proj_comp_ne_of_le {U S : LightProfinite.{0}} {g h : U ⟶ S} {k n : ℕ}
    (hkn : k ≤ n) (hne : g ≫ S.proj k ≠ h ≫ S.proj k) :
    g ≫ S.proj n ≠ h ≫ S.proj n := by
  intro H
  apply hne
  calc
    g ≫ S.proj k = g ≫ (S.proj n ≫ S.transitionMapLE hkn) := by
      rw [S.proj_comp_transitionMapLE hkn]
    _ = (g ≫ S.proj n) ≫ S.transitionMapLE hkn := by rw [Category.assoc]
    _ = (h ≫ S.proj n) ≫ S.transitionMapLE hkn := by rw [H]
    _ = h ≫ (S.proj n ≫ S.transitionMapLE hkn) := by rw [Category.assoc]
    _ = h ≫ S.proj k := by rw [S.proj_comp_transitionMapLE hkn]

/-- A finite set of maps into a light profinite space is separated by one finite quotient. -/
lemma exists_proj_injective_on_finset_hom (U S : LightProfinite.{0}) (t : Finset (U ⟶ S)) :
    ∃ n : ℕ, Set.InjOn (fun g : U ⟶ S => g ≫ S.proj n) (↑t : Set (U ⟶ S)) := by
  classical
  let sep : (U ⟶ S) × (U ⟶ S) → ℕ := fun p =>
    if h : p.1 ≠ p.2 then Classical.choose (exists_proj_comp_ne_of_ne h) else 0
  let N := (t.product t).sup sep
  refine ⟨N, ?_⟩
  intro g hg h hh H
  by_contra hne
  have hsep : g ≫ S.proj (sep (g, h)) ≠ h ≫ S.proj (sep (g, h)) := by
    dsimp [sep]
    rw [dif_pos hne]
    exact Classical.choose_spec (exists_proj_comp_ne_of_ne hne)
  have hle : sep (g, h) ≤ N := by
    dsimp [N]
    exact Finset.le_sup (s := t.product t) (f := sep) (b := (g, h)) (by
      exact (Finset.mem_product).mpr ⟨hg, hh⟩)
  exact proj_comp_ne_of_le hle hsep H

/-- A finite set of points in a light profinite space is separated by one finite quotient. -/
lemma exists_proj_injective_on_finset_points (S : LightProfinite.{0}) (t : Finset S) :
    ∃ n : ℕ, Set.InjOn (fun s : S => S.proj n s) (↑t : Set S) := by
  classical
  let X : LightProfinite.{0} := LightProfinite.of PUnit
  let c : S → (X ⟶ S) := fun s => X.const s
  obtain ⟨n, hn⟩ := exists_proj_injective_on_finset_hom X S (t.image c)
  refine ⟨n, ?_⟩
  intro x hx y hy hxy
  have hcx : c x ∈ t.image c := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hcy : c y ∈ t.image c := Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hcproj : c x ≫ S.proj n = c y ≫ S.proj n := by
    ext p
    exact hxy
  have hc : c x = c y := hn hcx hcy hcproj
  have hpt := ConcreteCategory.congr_hom hc PUnit.unit
  have hx : c x PUnit.unit = x := rfl
  have hy : c y PUnit.unit = y := rfl
  simpa [hx, hy] using hpt

end LightProfinite

namespace LightCondensed

/-- The `ModuleCat`-valued presheaf of continuous maps from light profinite test objects into a
topological abelian group. -/
noncomputable def topModulePresheaf (M : TopModuleCat.{0} ℤ) :
    LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ where
  obj S := ModuleCat.of ℤ C(↑S.unop.toTop, M)
  map {S T} f := by
    let φ : C(↑T.unop.toTop, ↑S.unop.toTop) := f.unop.hom.hom
    exact ModuleCat.ofHom {
      toFun := fun g => g.comp φ
      map_add' := by intro x y; ext s; rfl
      map_smul' := by intro r x; ext s; rfl }
  map_id := by intro S; ext f s; rfl
  map_comp := by intro S T U f g; ext h s; rfl

/-- Forgetting the module structure on `topModulePresheaf` gives the usual light-condensed set
associated to the underlying topological space. -/
noncomputable def topModulePresheafForgetIso (M : TopModuleCat.{0} ℤ) :
    topModulePresheaf M ⋙ CategoryTheory.forget (ModuleCat.{0} ℤ) ≅
      (topCatToLightCondSet.obj ((forget₂ (TopModuleCat ℤ) TopCat).obj M)).obj := by
  refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
  intro S T f
  ext x
  rfl

noncomputable instance (M : TopModuleCat.{0} ℤ) :
    PreservesFiniteProducts (topModulePresheaf M ⋙ CategoryTheory.forget (ModuleCat.{0} ℤ)) where
  preserves n := by
    let G := (topCatToLightCondSet.obj ((forget₂ (TopModuleCat ℤ) TopCat).obj M)).obj
    haveI : PreservesFiniteProducts G := inferInstance
    exact preservesLimitsOfShape_of_natIso (J := Discrete (Fin n))
      (topModulePresheafForgetIso M).symm

/-- The light condensed abelian group represented by a topological abelian group. -/
noncomputable def topModuleToLightCondAbObj (M : TopModuleCat.{0} ℤ) : LightCondAb := by
  refine LightCondensed.ofSheafForgetLightProfinite (topModulePresheaf M) ?_
  exact regularTopology.equalizerCondition_of_natIso (topModulePresheafForgetIso M).symm
    (LightCondensed.equalizerCondition
      (topCatToLightCondSet.obj ((forget₂ (TopModuleCat ℤ) TopCat).obj M)))

/-- Postcomposition of continuous maps gives functoriality of `topModuleToLightCondAbObj`. -/
noncomputable def topModuleToLightCondAbMap {M N : TopModuleCat.{0} ℤ} (f : M ⟶ N) :
    topModuleToLightCondAbObj M ⟶ topModuleToLightCondAbObj N where
  hom := {
    app S := by
      let φ : C(M, N) := ⟨f.hom, f.hom.continuous⟩
      exact ModuleCat.ofHom {
        toFun := fun g => φ.comp g
        map_add' := by intro x y; ext s; simp [φ]
        map_smul' := by intro r x; ext s; simp [φ] }
    naturality := by
      intro S T φ
      ext g
      rfl }

/-- The underlying light condensed set of the light condensed abelian group represented by a
topological abelian group is the usual light condensed set represented by its underlying
space. -/
noncomputable def topModuleToLightCondAbForgetIso (M : TopModuleCat.{0} ℤ) :
    (forget ℤ).obj (topModuleToLightCondAbObj M) ≅
      topCatToLightCondSet.obj ((forget₂ (TopModuleCat ℤ) TopCat).obj M) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (topModulePresheafForgetIso M)

@[simp]
lemma topModuleToLightCondAbForgetIso_hom_app (M : TopModuleCat.{0} ℤ)
    (S : LightProfiniteᵒᵖ)
    (x : ((forget ℤ).obj (topModuleToLightCondAbObj M)).obj.obj S) :
    (topModuleToLightCondAbForgetIso M).hom.hom.app S x = x := rfl

@[simp]
lemma topModuleToLightCondAbForgetIso_inv_app (M : TopModuleCat.{0} ℤ)
    (S : LightProfiniteᵒᵖ)
    (x : (topCatToLightCondSet.obj ((forget₂ (TopModuleCat ℤ) TopCat).obj M)).obj.obj S) :
    (topModuleToLightCondAbForgetIso M).inv.hom.app S x = x := rfl

/-- The functor from topological abelian groups to light condensed abelian groups. -/
noncomputable def topModuleToLightCondAb : TopModuleCat.{0} ℤ ⥤ LightCondAb where
  obj M := topModuleToLightCondAbObj M
  map {M N} f := topModuleToLightCondAbMap f
  map_id := by
    intro M
    ext S g
    rfl
  map_comp := by
    intro M N K f g
    ext S h
    rfl

end LightCondensed

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- The Markov/Graev free topological abelian group on the underlying topological space of `S`. -/
abbrev topologicalFree : TopModuleCat.{0} ℤ :=
  (TopModuleCat.free ℤ).obj S.toTop

/-- The light condensed abelian group represented by the topological free abelian group on `S`. -/
abbrev topologicalFreeCondensed : LightCondAb :=
  LightCondensed.topModuleToLightCondAbObj (topologicalFree S)

/-- The Dirac map from `S` into its free topological abelian group. -/
abbrev topologicalFreeDirac : S.toTop ⟶ (forget₂ (TopModuleCat ℤ) TopCat).obj (topologicalFree S) :=
  (TopModuleCat.freeAdj ℤ).unit.app S.toTop

@[simp]
lemma topologicalFreeDirac_apply (s : S) :
    (topologicalFreeDirac S) s = Finsupp.single s (1 : ℤ) := rfl

/-- The presheaf freely generated by the represented light condensed set `S`. -/
abbrev freePresheaf (S : LightProfinite.{0}) : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ :=
  S.toCondensed.obj ⋙ ModuleCat.free ℤ

/-- The `ModuleCat`-valued presheaf represented by the topological free abelian group on `S`. -/
abbrev topologicalFreePresheaf (S : LightProfinite.{0}) :
    LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ :=
  LightCondensed.topModulePresheaf (topologicalFree S)

/-- The continuous Dirac section attached to a generator of the free presheaf. -/
noncomputable def freePresheafToTopologicalFreePresheafGenerator
    (S : LightProfinite.{0}) (U : LightProfiniteᵒᵖ)
    (g : S.toCondensed.obj.obj U) : (topologicalFreePresheaf S).obj U :=
  (show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from
    (topologicalFreeDirac S).hom.comp g.hom.hom)

/-- The presheaf-level comparison from formal sums of maps into `S` to represented sections of the
free topological abelian group on `S`. -/
noncomputable def freePresheafToTopologicalFreePresheaf (S : LightProfinite.{0}) :
    freePresheaf S ⟶ topologicalFreePresheaf S where
  app U := ModuleCat.freeDesc (R := ℤ)
    (↾freePresheafToTopologicalFreePresheafGenerator S U)
  naturality := by
    intro U V f
    apply ModuleCat.free_hom_ext
    intro g
    change (((ModuleCat.free ℤ).map (S.toCondensed.obj.map f) ≫
        ModuleCat.freeDesc (R := ℤ)
          (↾freePresheafToTopologicalFreePresheafGenerator S V)) (ModuleCat.freeMk g)) =
      ((ModuleCat.freeDesc (R := ℤ)
          (↾freePresheafToTopologicalFreePresheafGenerator S U) ≫
        (LightCondensed.topModulePresheaf (topologicalFree S)).map f) (ModuleCat.freeMk g))
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    rw [show (ModuleCat.freeDesc (R := ℤ)
        (↾freePresheafToTopologicalFreePresheafGenerator S U)) (ModuleCat.freeMk g) =
        freePresheafToTopologicalFreePresheafGenerator S U g from
      ModuleCat.freeDesc_apply (↾freePresheafToTopologicalFreePresheafGenerator S U) g]
    change (ModuleCat.freeDesc (R := ℤ)
        (↾freePresheafToTopologicalFreePresheafGenerator S V))
        (ModuleCat.freeMk ((S.toCondensed.obj.map f) g)) =
      ((LightCondensed.topModulePresheaf (topologicalFree S)).map f)
        (freePresheafToTopologicalFreePresheafGenerator S U g)
    rw [show (ModuleCat.freeDesc (R := ℤ)
        (↾freePresheafToTopologicalFreePresheafGenerator S V))
        (ModuleCat.freeMk ((S.toCondensed.obj.map f) g)) =
        freePresheafToTopologicalFreePresheafGenerator S V ((S.toCondensed.obj.map f) g) from
      ModuleCat.freeDesc_apply (↾freePresheafToTopologicalFreePresheafGenerator S V)
        ((S.toCondensed.obj.map f) g)]
    apply ContinuousMap.ext
    intro u
    rfl

@[simp]
lemma freePresheafToTopologicalFreePresheaf_app_freeMk
    (S : LightProfinite.{0}) (U : LightProfiniteᵒᵖ)
    (g : S.toCondensed.obj.obj U) :
    (freePresheafToTopologicalFreePresheaf S).app U (ModuleCat.freeMk g) =
      freePresheafToTopologicalFreePresheafGenerator S U g := by
  exact ModuleCat.freeDesc_apply (↾freePresheafToTopologicalFreePresheafGenerator S U) g

@[simp]
lemma freePresheafToTopologicalFreePresheaf_apply_single
    (S U : LightProfinite.{0}) (g : U ⟶ S) (u : U) :
    ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ (Finsupp.single g (1 : ℤ))) u) =
      Finsupp.single (g u) (1 : ℤ) := by
  change ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
    (ModuleCat.freeDesc (R := ℤ)
      (↾freePresheafToTopologicalFreePresheafGenerator S (Opposite.op U)))
      (ModuleCat.freeMk g)) u) = Finsupp.single (g u) (1 : ℤ)
  rw [show (ModuleCat.freeDesc (R := ℤ)
      (↾freePresheafToTopologicalFreePresheafGenerator S (Opposite.op U)))
      (ModuleCat.freeMk g) =
      freePresheafToTopologicalFreePresheafGenerator S (Opposite.op U) g from
    ModuleCat.freeDesc_apply
      (↾freePresheafToTopologicalFreePresheafGenerator S (Opposite.op U)) g]
  rfl

lemma freePresheafToTopologicalFreePresheaf_naturality_apply
    (S : LightProfinite.{0}) {U V : LightProfiniteᵒᵖ} (f : U ⟶ V)
    (a : (freePresheaf S).obj U) :
    (freePresheafToTopologicalFreePresheaf S).app V ((freePresheaf S).map f a) =
      (topologicalFreePresheaf S).map f
        ((freePresheafToTopologicalFreePresheaf S).app U a) := by
  have h := congrArg (fun m => m a) ((freePresheafToTopologicalFreePresheaf S).naturality f)
  simpa [ModuleCat.comp_apply] using h

/-- Pointwise, the presheaf comparison sends a formal sum of maps `U ⟶ S` to the corresponding
finite signed measure on `S`.  This is the algebraic reduction used in the local-injectivity
argument: equality in the represented topological free group gives equality of these pushed-forward
finitely supported functions at every point of `U`. -/
lemma freePresheafToTopologicalFreePresheaf_apply
    (S U : LightProfinite.{0}) (a : (freePresheaf S).obj ⟨U⟩) (u : U) :
    ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a) u) =
      Finsupp.mapDomain (fun g : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from g) u)) a := by
  let L : ((freePresheaf S).obj ⟨U⟩) →ₗ[ℤ] (S →₀ ℤ) := {
    toFun := fun a => ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
      ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom a) u)
    map_add' := fun a b => by
      change ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
          ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom (a + b)) u) =
        ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
          ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom a) u) +
        ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
          ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom b) u)
      rw [LinearMap.map_add]
      rfl
    map_smul' := fun n a => by
      have h := congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
        ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from z) u))
        (LinearMap.map_smul ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom n a)
      change ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
          ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom (n • a)) u) =
        n • ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from
          ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom a) u)
      exact h.trans (ContinuousMap.smul_apply n (show C(↑U.toTop, ↑(topologicalFree S).toModuleCat)
        from ((freePresheafToTopologicalFreePresheaf S).app ⟨U⟩).hom a) u) }
  let R : ((freePresheaf S).obj ⟨U⟩) →ₗ[ℤ] (S →₀ ℤ) := {
    toFun := fun a =>
      Finsupp.mapDomain (fun g : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from g) u)) a
    map_add' := fun _ _ => Finsupp.mapDomain_add
    map_smul' := fun n a => by
      exact (Finsupp.mapDomain_smul
        (f := fun g : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from g) u)) n a) }
  change L a = R a
  suffices L = R by rw [this]
  refine Finsupp.lhom_ext' fun g => LinearMap.ext_ring ?_
  change L (Finsupp.single g (1 : ℤ)) = R (Finsupp.single g (1 : ℤ))
  dsimp [L, R]
  rw [freePresheafToTopologicalFreePresheaf_apply_single]
  change Finsupp.single ((show U ⟶ S from g) u) (1 : ℤ) =
    Finsupp.mapDomain (fun h : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from h) u))
      (Finsupp.single g (1 : ℤ))
  rw [Finsupp.mapDomain_single]

lemma freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq
    (S U : LightProfinite.{0}) {a b : (freePresheaf S).obj ⟨U⟩}
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b) (u : U) :
    Finsupp.mapDomain (fun g : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from g) u)) a =
      Finsupp.mapDomain (fun g : S.toCondensed.obj.obj ⟨U⟩ => ((show U ⟶ S from g) u)) b := by
  rw [← freePresheafToTopologicalFreePresheaf_apply S U a u,
    ← freePresheafToTopologicalFreePresheaf_apply S U b u]
  exact congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
    ((show C(↑U.toTop, ↑(topologicalFree S).toModuleCat) from z) u)) h

/-- A single effective epimorphism lying in an equalizer sieve gives a coherent covering of that
sieve.  This is the site-theoretic target for the finite closed-cover part of local injectivity. -/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpi
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U V : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (π : V ⟶ U) [EffectiveEpi π]
    (hπ : F.map π.op x = F.map π.op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  refine ⟨Unit, inferInstance, (fun _ => V), (fun _ => π), ?_, ?_⟩
  · simpa [CategoryTheory.effectiveEpi_iff_effectiveEpiFamily] using (inferInstance : EffectiveEpi π)
  · intro _
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ

/-- A closed subset of a light profinite space, with the induced topology, is light profinite. -/
noncomputable def closedSubLightProfinite {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    LightProfinite.{0} :=
  @LightProfinite.of s inferInstance (isCompact_iff_compactSpace.mp hs.isCompact)
    inferInstance inferInstance inferInstance

/-- The inclusion of a closed light-profinite subspace. -/
noncomputable def closedSubLightProfiniteι {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    closedSubLightProfinite s hs ⟶ X := by
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  exact CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma closedSubLightProfiniteι_apply {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s)
    (x : closedSubLightProfinite s hs) : closedSubLightProfiniteι s hs x = (x : s).1 := by
  change (ConcreteCategory.hom (closedSubLightProfiniteι s hs)) x = (x : s).1
  rw [show ConcreteCategory.hom (closedSubLightProfiniteι s hs) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)) by
    simp [closedSubLightProfiniteι, closedSubLightProfinite]]
  rfl

/-- A finite jointly-surjective family in `LightProfinite` is an effective-epi family. -/
lemma effectiveEpiFamily_of_jointly_surjective {α : Type} [Finite α]
    {B : LightProfinite.{0}} (X : α → LightProfinite.{0}) (π : (a : α) → X a ⟶ B)
    (hπ : ∀ b : B, ∃ a, ∃ x : X a, π a x = b) : EffectiveEpiFamily X π := by
  rw [← CategoryTheory.effectiveEpi_desc_iff_effectiveEpiFamily]
  rw [LightProfinite.effectiveEpi_iff_surjective]
  intro b
  obtain ⟨a, x, hx⟩ := hπ b
  refine ⟨Sigma.ι X a x, ?_⟩
  exact (ConcreteCategory.congr_hom (Sigma.ι_desc π a) x).trans hx

/-- A finite effective-epi family lying in an equalizer sieve gives a coherent covering of that
sieve. -/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (V : α → LightProfinite.{0}) (π : (a : α) → V a ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ a, F.map (π a).op x = F.map (π a).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun a => by
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ a⟩

/-- A finite effective-epi family with local preimages gives a coherent covering of the image
sieve. -/
lemma presheaf_imageSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun i => by
    simpa [CategoryTheory.Presheaf.imageSieve] using hπ i⟩

/-- A finite jointly-surjective family with local preimages gives a coherent covering of the image
sieve. -/
lemma presheaf_imageSieve_mem_of_finite_jointly_surjective
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    (hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u)
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact presheaf_imageSieve_mem_of_effectiveEpiFamily φ s V π hπ

/-- A finite closed cover whose inclusions lie in an equalizer sieve gives a coherent covering of
that sieve.  This packages the closed-cover replacement for the tempting but invalid clopen
refinement. -/
lemma freePresheaf_equalizerSieve_mem_of_finite_closed_cover
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (C : α → Set U) (hC : ∀ a, IsClosed (C a))
    (hcover : ∀ u : U, ∃ a, u ∈ C a)
    (hπ : ∀ a, F.map (closedSubLightProfiniteι (C a) (hC a)).op x =
      F.map (closedSubLightProfiniteι (C a) (hC a)).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun a => closedSubLightProfinite (C a) (hC a)
  let π : (a : α) → V a ⟶ U := fun a => closedSubLightProfiniteι (C a) (hC a)
  have hsurj : ∀ u : U, ∃ a, ∃ x : V a, π a x = u := by
    intro u
    obtain ⟨a, hu⟩ := hcover u
    refine ⟨a, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C a) (hC a) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily x y V π hπ

/-- Pulling back a presheaf equalizer sieve restricts the two sections along the same arrow. -/
lemma _root_.CategoryTheory.Presheaf.equalizerSieve_pullback_eq
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U V : LightProfinite.{0}} (π : V ⟶ U)
    (x y : F.obj ⟨U⟩) :
    (CategoryTheory.Presheaf.equalizerSieve x y).pullback π =
      CategoryTheory.Presheaf.equalizerSieve (F.map π.op x) (F.map π.op y) := by
  ext W f
  simp [CategoryTheory.Presheaf.equalizerSieve]

/-- If the equalizer sieve is covering locally on every member of a finite closed cover, then it is
covering on the original space.  This is the transitivity form of the closed-cover reduction. -/
lemma presheaf_equalizerSieve_mem_of_finite_closed_cover_locally
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩)
    (C : α → Set U) (hC : ∀ i, IsClosed (C i))
    (hcover : ∀ u : U, ∃ i, u ∈ C i)
    (hlocal : ∀ i,
      CategoryTheory.Presheaf.equalizerSieve
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op x)
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op y) ∈
          (coherentTopology LightProfinite)
            (closedSubLightProfinite (C i) (hC i))) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈
      (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun i => closedSubLightProfinite (C i) (hC i)
  let π : (i : α) → V i ⟶ U := fun i => closedSubLightProfiniteι (C i) (hC i)
  have hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u := by
    intro u
    obtain ⟨i, hu⟩ := hcover u
    refine ⟨i, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C i) (hC i) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  let S₀ : Sieve U := Sieve.ofArrows V π
  have hS₀ : S₀ ∈ (coherentTopology LightProfinite) U := by
    apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    exact ⟨α, inferInstance, V, π, inferInstance, fun i => Sieve.ofArrows_mk V π i⟩
  refine (coherentTopology LightProfinite).transitive hS₀
    (CategoryTheory.Presheaf.equalizerSieve x y) ?_
  intro Y f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff V π f).mp hf
  have hπ : (CategoryTheory.Presheaf.equalizerSieve x y).pullback (π i) ∈
      (coherentTopology LightProfinite) (V i) := by
    simpa [S₀, V, π, CategoryTheory.Presheaf.equalizerSieve_pullback_eq] using hlocal i
  simpa [Sieve.pullback_comp] using
    ((coherentTopology LightProfinite).pullback_stable g hπ)

/-- Equality-pattern loci cut out by finitely many equalities between maps to a light profinite
space are closed.  The second TFC3 round uses these as closed members of a coherent cover; the
remaining coefficient extraction happens after restricting the free presheaf to these loci. -/
lemma finiteMapEqualityPattern_isClosed {α : Type} [Finite α] {U S : LightProfinite.{0}}
    (f : α → (U ⟶ S)) (r : α → α → Prop) :
    IsClosed {u : U | ∀ i j, r i j → (f i) u = (f j) u} := by
  classical
  rw [show {u : U | ∀ i j, r i j → (f i) u = (f j) u} =
      ⋂ i, ⋂ j, ⋂ _h : r i j, {u : U | (f i) u = (f j) u} by
    ext u
    simp]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (f i).hom.hom.continuous (f j).hom.hom.continuous

/-- If `f` is injective on the union of the supports of two finitely supported functions, equality
after `Finsupp.mapDomain f` reflects equality. -/
lemma finsupp_mapDomain_eq_of_eq_of_injOn_support_union {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) {a b : α →₀ ℤ}
    (hinj : Set.InjOn f ((↑((a.support : Finset α) ∪ b.support) : Set α)))
    (h : Finsupp.mapDomain f a = Finsupp.mapDomain f b) : a = b := by
  ext x
  by_cases hx : x ∈ (a.support : Finset α) ∪ b.support
  · have ha : (Finsupp.mapDomain f a) (f x) = a x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_left _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : a x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    have hb : (Finsupp.mapDomain f b) (f x) = b x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_right _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : b x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    exact ha ▸ hb ▸ DFunLike.congr_fun h (f x)
  · have hxa : x ∉ a.support := fun hxa => hx (Finset.mem_union_left _ hxa)
    have hxb : x ∉ b.support := fun hxb => hx (Finset.mem_union_right _ hxb)
    have hax : a x = 0 := by
      by_contra hne
      exact hxa ((Finsupp.mem_support_iff).mpr hne)
    have hbx : b x = 0 := by
      by_contra hne
      exact hxb ((Finsupp.mem_support_iff).mpr hne)
    simp [hax, hbx]

/-- If a finitely supported integer combination vanishes after `mapDomain`, then every support
point collides under the domain map with another support point. -/
lemma finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (c : α →₀ ℤ) {x : α} (hx : x ∈ c.support)
    (f : α → β) (hzero : Finsupp.mapDomain f c = 0) :
    ∃ y, y ∈ c.support ∧ y ≠ x ∧ f y = f x := by
  by_contra hnone
  have hsum : (Finsupp.mapDomain f c) (f x) = c x := by
    rw [Finsupp.mapDomain_apply_eq_sum]
    refine Finset.sum_eq_single x ?_ ?_
    · intro y hy hyx
      rw [Finset.mem_filter] at hy
      exact (hnone ⟨y, hy.1, hyx, hy.2⟩).elim
    · intro hxnot
      exact (hxnot (by
        rw [Finset.mem_filter]
        exact ⟨hx, rfl⟩)).elim
  have hzero_apply : (Finsupp.mapDomain f c) (f x) = 0 := by
    rw [hzero]
    rfl
  rw [hsum] at hzero_apply
  exact (Finsupp.mem_support_iff.mp hx) hzero_apply

/-- If two distinct support points collide under the domain map, then the support of the
`mapDomain` result has strictly smaller cardinality.  This only uses the upper bound by the image
of the original support, so cancellations after `mapDomain` are allowed. -/
lemma finsupp_mapDomain_support_card_lt_of_pair_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (c : α →₀ ℤ)
    {x y : α} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hne : x ≠ y) (hxy : f x = f y) :
    (Finsupp.mapDomain f c).support.card < c.support.card := by
  have hsubset : (Finsupp.mapDomain f c).support ⊆ c.support.image f := by
    exact Finsupp.mapDomain_support
  have hcard_support : (Finsupp.mapDomain f c).support.card ≤ (c.support.image f).card :=
    Finset.card_le_card hsubset
  have hnotinj : ¬ Set.InjOn f (c.support : Set α) := by
    intro hinj
    exact hne (hinj (by exact Finset.mem_coe.mpr hx) (by exact Finset.mem_coe.mpr hy) hxy)
  have hcard_image_lt : (c.support.image f).card < c.support.card := by
    have hle : (c.support.image f).card ≤ c.support.card := Finset.card_image_le
    have hnecard : (c.support.image f).card ≠ c.support.card := by
      intro heq
      exact hnotinj ((Finset.card_image_iff (s := c.support) (f := f)).mp heq)
    exact Nat.lt_of_le_of_ne hle hnecard
  exact lt_of_le_of_lt hcard_support hcard_image_lt

lemma freePresheaf_map_sub
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (a b : (freePresheaf S).obj ⟨U⟩) :
    (freePresheaf S).map π.op (a - b) =
      (freePresheaf S).map π.op a - (freePresheaf S).map π.op b := by
  exact ((freePresheaf S).map π.op).hom.map_sub a b

lemma freePresheaf_restrict_support_card_lt_of_eq_on_pair
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (c : (freePresheaf S).obj ⟨U⟩)
    {g h : U ⟶ S} (hg : g ∈ c.support) (hh : h ∈ c.support)
    (hne : g ≠ h) (heq : π ≫ g = π ≫ h) :
    (((freePresheaf S).map π.op c).support.card < c.support.card) := by
  classical
  change (Finsupp.mapDomain (fun g : U ⟶ S => π ≫ g) c).support.card < c.support.card
  exact finsupp_mapDomain_support_card_lt_of_pair_eq (fun g : U ⟶ S => π ≫ g) c hg hh hne heq

lemma freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero
    (S U : LightProfinite.{0}) {a b : (freePresheaf S).obj ⟨U⟩}
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b)
    (u : U) :
    Finsupp.mapDomain (fun g : U ⟶ S => g u) (a - b) = 0 := by
  classical
  let f : S.toCondensed.obj.obj ⟨U⟩ → S :=
    fun g => ((show U ⟶ S from g) u)
  change Finsupp.mapDomain f (a - b) = 0
  have hpoint : Finsupp.mapDomain f a = Finsupp.mapDomain f b := by
    simpa [f] using freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq S U h u
  calc
    Finsupp.mapDomain f (a - b) = Finsupp.mapDomain f a - Finsupp.mapDomain f b := by
      exact Finsupp.mapDomain_sub
    _ = 0 := by simp [hpoint]

/-- Indices for the one-step collision cover: support maps distinct from the chosen `g₀`. -/
def freePresheaf_collisionCoverIndex
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) : Type :=
  {g : S.toCondensed.obj.obj ⟨U⟩ // g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}

instance freePresheaf_collisionCoverIndex_finite
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    Finite (freePresheaf_collisionCoverIndex S U c g₀) := by
  classical
  let collisionSet : Set (S.toCondensed.obj.obj ⟨U⟩) :=
    {g | g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}
  have hfinite : collisionSet.Finite := by
    refine Set.Finite.ofFinset
      (c.support.filter fun g => (show U ⟶ S from g) ≠ g₀) ?_
    intro g
    simp [collisionSet]
  change Finite collisionSet
  exact hfinite.to_subtype

/-- The closed equality locus for a collision-cover index. -/
noncomputable def freePresheaf_collisionCoverSet
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    freePresheaf_collisionCoverIndex S U c g₀ → Set U :=
  fun g => {u | (show U ⟶ S from g.1) u = g₀ u}

lemma freePresheaf_collisionCover_isClosed
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    ∀ i, IsClosed (freePresheaf_collisionCoverSet S U c g₀ i) := by
  intro i
  exact isClosed_eq (show U ⟶ S from i.1).hom.hom.continuous g₀.hom.hom.continuous

lemma freePresheaf_collisionCover_covers_of_pointwise_zero
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (hzero : ∀ u : U,
      Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0) :
    ∀ u : U, ∃ i, u ∈ freePresheaf_collisionCoverSet S U c g₀ i := by
  classical
  intro u
  obtain ⟨g, hg, hne, heq⟩ :=
    finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero c hg₀
      (fun g : U ⟶ S => g u) (hzero u)
  exact ⟨⟨g, hg, hne⟩, heq⟩

lemma freePresheaf_collisionCover_restrict_card_lt
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (i : freePresheaf_collisionCoverIndex S U c g₀) :
    let C := freePresheaf_collisionCoverSet S U c g₀ i
    let hC := freePresheaf_collisionCover_isClosed S U c g₀ i
    (((freePresheaf S).map (closedSubLightProfiniteι C hC).op c).support.card <
      c.support.card) := by
  classical
  dsimp only
  apply freePresheaf_restrict_support_card_lt_of_eq_on_pair S
    (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
      (freePresheaf_collisionCover_isClosed S U c g₀ i)) c i.2.1 hg₀ i.2.2
  ext x
  change (show U ⟶ S from i.1)
      (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x) =
    g₀ (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x)
  rw [closedSubLightProfiniteι_apply]
  exact (x : freePresheaf_collisionCoverSet S U c g₀ i).2

lemma freePresheafToTopologicalFreePresheaf_equalizerSieve_mem
    (S U : LightProfinite.{0})
    (a b : (freePresheaf S).obj ⟨U⟩)
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b) :
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U := by
  classical
  let P : ℕ → Prop := fun n => ∀ (U : LightProfinite.{0})
      (a b : (freePresheaf S).obj ⟨U⟩),
    (a - b).support.card = n →
    (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b →
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U
  have hind : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U a b hcard h
      by_cases hn : n = 0
      · have hcard0 : (a - b).support.card = 0 := hcard.trans hn
        have hempty : (a - b).support = ∅ := Finset.card_eq_zero.mp hcard0
        have hsub : a - b = 0 := Finsupp.support_eq_empty.mp hempty
        have hab : a = b := sub_eq_zero.mp hsub
        subst b
        rw [CategoryTheory.Presheaf.equalizerSieve_self_eq_top]
        exact (coherentTopology LightProfinite).top_mem U
      · have hcard_ne : (a - b).support.card ≠ 0 := by
          intro hzero
          exact hn (hcard.symm.trans hzero)
        obtain ⟨g₀, hg₀⟩ :=
          (Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne) : (a - b).support.Nonempty)
        let c : (freePresheaf S).obj ⟨U⟩ := a - b
        have hg₀c : g₀ ∈ c.support := by
          change g₀ ∈ (a - b).support
          exact hg₀
        let I := freePresheaf_collisionCoverIndex S U c g₀
        haveI : Finite I := freePresheaf_collisionCoverIndex_finite S U c g₀
        let C : I → Set U := freePresheaf_collisionCoverSet S U c g₀
        let hC : ∀ i, IsClosed (C i) := freePresheaf_collisionCover_isClosed S U c g₀
        have hzero : ∀ u : U, Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0 := by
          intro u
          simpa [c] using
            freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero S U h u
        have hcover : ∀ u : U, ∃ i, u ∈ C i := by
          simpa [c, C] using
            freePresheaf_collisionCover_covers_of_pointwise_zero S U c hg₀c hzero
        refine presheaf_equalizerSieve_mem_of_finite_closed_cover_locally a b C hC hcover ?_
        intro i
        let V : LightProfinite.{0} := closedSubLightProfinite (C i) (hC i)
        let π : V ⟶ U := closedSubLightProfiniteι (C i) (hC i)
        let aV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op a
        let bV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op b
        have hres : (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ aV =
            (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ bV := by
          exact (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op a).trans
            ((congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
              (topologicalFreePresheaf S).map π.op z) h).trans
            (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op b).symm)
        have hdropc : (((freePresheaf S).map π.op c).support.card < c.support.card) := by
          simpa [c, I, C, hC, V, π] using
            freePresheaf_collisionCover_restrict_card_lt S U c hg₀c i
        have hmap_sub : (freePresheaf S).map π.op c = aV - bV := by
          exact freePresheaf_map_sub S π a b
        have hdrop : (aV - bV).support.card < n := by
          calc
            (aV - bV).support.card = ((freePresheaf S).map π.op c).support.card := by
              rw [← hmap_sub]
            _ < c.support.card := hdropc
            _ = n := by simpa [c] using hcard
        exact ih (aV - bV).support.card hdrop V aV bV rfl hres
  exact hind (a - b).support.card U a b rfl h

instance freePresheafToTopologicalFreePresheaf_isLocallyInjective
    (S : LightProfinite.{0}) :
    CategoryTheory.Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  refine ⟨?_⟩
  intro Uop a b h
  rcases Uop with ⟨U⟩
  change CategoryTheory.Presheaf.equalizerSieve a b ∈ (coherentTopology LightProfinite) U
  exact freePresheafToTopologicalFreePresheaf_equalizerSieve_mem S U a b h

/-- For a finite target, the presheaf comparison is locally injective.  The covering pieces are the
closed loci on which every support map of the two sections is constant. -/
instance freePresheafToTopologicalFreePresheaf_isLocallyInjective_of_finite
    (S : LightProfinite.{0}) [Finite S] :
    CategoryTheory.Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  classical
  refine ⟨?_⟩
  intro Uop a b h
  rcases Uop with ⟨U⟩
  change CategoryTheory.Presheaf.equalizerSieve a b ∈ (coherentTopology LightProfinite) U
  let supp : Finset (U ⟶ S) := (a.support : Finset (U ⟶ S)) ∪ b.support
  let α := { c : supp → S // ∃ u : U, ∀ g : supp, (g : U ⟶ S) u = c g }
  haveI : Finite α := by dsimp [α]; infer_instance
  let C : α → Set U := fun c => {u : U | ∀ g : supp, (g : U ⟶ S) u = c.1 g}
  have hC : ∀ c, IsClosed (C c) := by
    intro c
    rw [show C c = ⋂ g : supp, {u : U | (g : U ⟶ S) u = c.1 g} by
      ext u
      simp [C]]
    exact isClosed_iInter fun g => isClosed_eq (g : U ⟶ S).hom.hom.continuous continuous_const
  have hcover : ∀ u : U, ∃ c, u ∈ C c := by
    intro u
    refine ⟨⟨fun g : supp => (g : U ⟶ S) u, ⟨u, fun g => rfl⟩⟩, ?_⟩
    intro g
    rfl
  apply freePresheaf_equalizerSieve_mem_of_finite_closed_cover a b C hC hcover
  intro c
  let V : LightProfinite.{0} := closedSubLightProfinite (C c) (hC c)
  let π : V ⟶ U := closedSubLightProfiniteι (C c) (hC c)
  let a' : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op a
  let b' : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op b
  change a' = b'
  obtain ⟨u0, hu0⟩ := c.2
  let v0 : V := ⟨u0, hu0⟩
  have hres : (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ a' =
      (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ b' := by
    exact (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op a).trans
      ((congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
        (topologicalFreePresheaf S).map π.op z) h).trans
      (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op b).symm)
  have hpoint := freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq S V hres v0
  apply finsupp_mapDomain_eq_of_eq_of_injOn_support_union
    (fun r : V ⟶ S => r v0) ?_ hpoint
  intro r hr t ht hrt
  have hconst : ∀ q : S.toCondensed.obj.obj ⟨V⟩,
      q ∈ a'.support ∪ b'.support → ∀ x y : V,
        (show V ⟶ S from q) x = (show V ⟶ S from q) y := by
    intro q hq x y
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · have himg : q ∈ Finset.image (fun g : U ⟶ S => π ≫ g) a.support :=
        Finsupp.mapDomain_support hq
      obtain ⟨g, hg, hgq⟩ := Finset.mem_image.mp himg
      have hgq' : π ≫ g = q := hgq
      have hxs : g (π x) = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := by
        have hxmem : (π x) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) x ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (x : C c).2
        exact hxmem ⟨g, Finset.mem_union_left b.support hg⟩
      have hys : g (π y) = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := by
        have hymem : (π y) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) y ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (y : C c).2
        exact hymem ⟨g, Finset.mem_union_left b.support hg⟩
      calc
        (show V ⟶ S from q) x = g (π x) := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' x).symm
        _ = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := hxs
        _ = g (π y) := hys.symm
        _ = (show V ⟶ S from q) y := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' y)
    · have himg : q ∈ Finset.image (fun g : U ⟶ S => π ≫ g) b.support :=
        Finsupp.mapDomain_support hq
      obtain ⟨g, hg, hgq⟩ := Finset.mem_image.mp himg
      have hgq' : π ≫ g = q := hgq
      have hxs : g (π x) = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := by
        have hxmem : (π x) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) x ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (x : C c).2
        exact hxmem ⟨g, Finset.mem_union_right a.support hg⟩
      have hys : g (π y) = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := by
        have hymem : (π y) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) y ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (y : C c).2
        exact hymem ⟨g, Finset.mem_union_right a.support hg⟩
      calc
        (show V ⟶ S from q) x = g (π x) := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' x).symm
        _ = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := hxs
        _ = g (π y) := hys.symm
        _ = (show V ⟶ S from q) y := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' y)
  ext x
  have hr' : r ∈ (a'.support : Finset (V ⟶ S)) ∪ b'.support := Finset.mem_coe.mp hr
  have ht' : t ∈ (a'.support : Finset (V ⟶ S)) ∪ b'.support := Finset.mem_coe.mp ht
  calc
    r x = r v0 := hconst r hr' x v0
    _ = t v0 := hrt
    _ = t x := (hconst t ht' x v0).symm

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

/-- Evaluation on topological free abelian groups is natural in the light profinite source. -/
lemma topologicalFreeEval_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeMap f ≫ topologicalFreeEval T g =
      topologicalFreeEval S (g.comap f.hom.hom) := by
  ext μ
  let L : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeMap f ≫ topologicalFreeEval T g).hom.toLinearMap
  let R : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeEval S (g.comap f.hom.hom)).hom.toLinearMap
  change L μ = R μ
  suffices L = R by rw [this]
  refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
  change (topologicalFreeEval T g).hom ((topologicalFreeMap f).hom (Finsupp.single s (1 : ℤ))) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom (Finsupp.single s (1 : ℤ))
  rw [topologicalFreeMap_single, topologicalFreeEval_single, topologicalFreeEval_single]
  rfl

/-- The induced morphism between represented light condensed abelian groups. -/
noncomputable def topologicalFreeEvalCondensed (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      LightCondensed.topModuleToLightCondAbObj discreteIntTopModule :=
  LightCondensed.topModuleToLightCondAbMap (topologicalFreeEval S f)

/-- The induced morphism from the represented topological free abelian group to the discrete
light condensed abelian group `ℤ`. -/
noncomputable def topologicalFreeEvalDiscrete (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom

/-- Represented topological-free evaluation is natural in the light profinite source. -/
lemma topologicalFreeEvalCondensed_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g =
      topologicalFreeEvalCondensed S (g.comap f.hom.hom) := by
  ext U h
  change (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g).hom.app U h) =
    (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeEvalCondensed S (g.comap f.hom.hom)).hom.app U h)
  ext u
  change (topologicalFreeEval T g).hom
      ((topologicalFreeMap f).hom
        ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)
  have hn := congrArg (fun m : topologicalFree S ⟶ discreteIntTopModule => m.hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u))
    (topologicalFreeEval_naturality f g)
  simpa using hn

/-- `Z`-valued represented topological-free evaluation is natural in the light profinite source. -/
lemma topologicalFreeEvalDiscrete_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalDiscrete T g =
      topologicalFreeEvalDiscrete S (g.comap f.hom.hom) := by
  simpa [topologicalFreeEvalDiscrete, Category.assoc] using
    congrArg (fun m => m ≫ discreteIntTopModuleCondensedIso.hom)
      (topologicalFreeEvalCondensed_naturality f g)

/-- The represented evaluation induced by `f` sends the Dirac section to `f`. -/
lemma topologicalFreeEvalDiscrete_diracSection (f : LocallyConstant S ℤ) :
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      ((topologicalFreeEvalDiscrete S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))) = f := by
  rw [show topologicalFreeEvalDiscrete S f =
    topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom by rfl]
  change ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      (discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩
        ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
          ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  rw [discreteIntTopModuleCondensedIso_sections]
  change (show LocallyConstant S ℤ from discreteIntTopModuleSectionsEquiv S
      ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  ext s
  dsimp [discreteIntTopModuleSectionsEquiv, discreteIntTopModulePresheafIso,
    topologicalFreeEvalCondensed]
  change (topologicalFreeEval S f).hom
      ((show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) s) = f s
  rw [topologicalFreeDiracSection_yoneda_apply]
  exact topologicalFreeEval_single S f s

/-- The sheaf-level morphism induced by the presheaf comparison from formal free sections to
represented topological-free sections. -/
noncomputable def freePresheafComparisonSheafification :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S where
  hom := CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

@[reassoc (attr := simp)]
lemma toSheafify_freePresheafComparisonSheafification :
    CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom =
    freePresheafToTopologicalFreePresheaf S := by
  exact CategoryTheory.toSheafify_sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

/-- At the represented identity section, the free/sheaf adjunction unit is the sheafification of
the presheaf free generator. -/
lemma freeForgetAdjunction_unit_app_id :
    ((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S) =
      (CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S)) := by
  rw [LightCondensed.freeForgetAdjunction, CategoryTheory.Sheaf.adjunction_unit_app_hom]
  rfl

/-- The sheafified presheaf comparison sends the represented Dirac generator to the represented
topological Dirac section. -/
lemma freePresheafComparison_diracSection :
    (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S) := by
  have h := congrArg (fun η : freePresheaf S ⟶ topologicalFreePresheaf S =>
      η.app ⟨S⟩ (ModuleCat.freeMk (𝟙 S)))
    (toSheafify_freePresheafComparisonSheafification S)
  change ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  exact h.trans (by
    change (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (freePresheafToTopologicalFreePresheaf S).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
      (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))
    rw [freePresheafToTopologicalFreePresheaf_app_freeMk]
    ext s
    rw [topologicalFreeDiracSection_yoneda_apply]
    rfl)

/-- Under the free/forget adjunction, the sheafified presheaf comparison is characterized by the
represented topological Dirac section. -/
lemma freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freePresheafComparisonSheafification S) = topologicalFreeDiracSection S := by
  apply (coherentTopology LightProfinite).yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  change (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      (((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S)) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  rw [freeForgetAdjunction_unit_app_id]
  exact freePresheafComparison_diracSection S

/-- The canonical comparison from the free light condensed abelian group to the light condensed
abelian group represented by the free topological abelian group. -/
noncomputable def freeToTopologicalFree :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)).symm
    (topologicalFreeDiracSection S)

@[simp]
lemma freeForgetAdjunction_homEquiv_freeToTopologicalFree :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freeToTopologicalFree S) = topologicalFreeDiracSection S := by
  simp [freeToTopologicalFree]

/-- The existing `freeToTopologicalFree` morphism is the sheaf-level morphism induced by the
presheaf comparison. -/
lemma freeToTopologicalFree_eq_sheafified_presheaf_comparison :
    freeToTopologicalFree S = freePresheafComparisonSheafification S := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed S)).injective
  rw [freeForgetAdjunction_homEquiv_freeToTopologicalFree,
    freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification]

/-- The comparison from the free light condensed abelian group to the represented topological free
abelian group is natural in the light profinite source. -/
lemma freeToTopologicalFree_naturality {S T : LightProfinite.{0}} (f : S ⟶ T) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ freeToTopologicalFree T =
      freeToTopologicalFree S ≫ topologicalFreeCondensedMap f := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed T)).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeToTopologicalFree]
  simp
  exact topologicalFreeDiracSection_naturality f

/-- The represented topological-free sheaf is isomorphic to its sheafification. -/
private noncomputable def topologicalFreeCondensedSheafifyIso (S : LightProfinite.{0}) :
    topologicalFreeCondensed S ≅
      (CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).obj
        (topologicalFreePresheaf S) where
  hom := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).hom)
  inv := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).inv)
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).inv_hom_id

/-- The sheafified presheaf comparison is the comparison followed by the inverse sheafification
identification of the represented target. -/
private lemma sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv
    (S : LightProfinite.{0}) :
    (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S)) ≫
        (topologicalFreeCondensedSheafifyIso S).inv) =
      freePresheafComparisonSheafification S := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [topologicalFreeCondensedSheafifyIso]
  rw [CategoryTheory.isoSheafify_inv]
  change CategoryTheory.sheafifyMap (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) ≫
        CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
          (𝟙 (topologicalFreePresheaf S)) (topologicalFreeCondensed S).property =
      CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
        (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property
  rw [CategoryTheory.sheafifyMap_sheafifyLift]
  simp

private instance instIsIso_sheafifiedPresheafComparison (S : LightProfinite.{0}) :
    IsIso (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S))) := by
  rw [← CategoryTheory.GrothendieckTopology.W_iff]
  exact (coherentTopology LightProfinite).W_of_isLocallyBijective
    (freePresheafToTopologicalFreePresheaf S)

instance instIsIso_freeToTopologicalFree (S : LightProfinite.{0}) :
    IsIso (freeToTopologicalFree S) := by
  rw [freeToTopologicalFree_eq_sheafified_presheaf_comparison]
  rw [← sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv]
  exact IsIso.comp_isIso' (instIsIso_sheafifiedPresheafComparison S) (Iso.isIso_inv _)

noncomputable def freeTopologicalFreeIso (S : LightProfinite.{0}) :
    (free ℤ).obj S.toCondensed ≅ topologicalFreeCondensed S :=
  asIso (freeToTopologicalFree S)

lemma freeTopologicalFreeIso_hom (S : LightProfinite.{0}) :
    (freeTopologicalFreeIso S).hom = freeToTopologicalFree S := by
  rfl

abbrev freeLightProfiniteMap : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ⟶
    sequentialToLightCondSet.obj (lightCondSetToSequential.obj
      ((forget ℤ).obj ((free ℤ).obj S.toCondensed))) :=
  LightCondSet.sequentialAdjunction.unit.app <| (forget ℤ).obj <| (free ℤ).obj S.toCondensed

namespace FreeImage

open LightProfinite.FreeImage

def iso : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ≅
    sequentialToLightCondSet.obj (sequential S) := sorry

end FreeImage

/-- The sequential finite-measure model for the free light condensed abelian group on `S`. -/
abbrev freeMeasureSequential : Sequential :=
  LightProfinite.FreeImage.sequential S

/-- The comparison isomorphism from the underlying light condensed set of `ℤ[S]` to the sequential
finite-measure model.  The proof is currently the main remaining comparison input in this file. -/
noncomputable def freeMeasureModelIso :
    (forget ℤ).obj ((free ℤ).obj S.toCondensed) ≅
      sequentialToLightCondSet.obj (freeMeasureSequential S) :=
  FreeImage.iso S

instance : IsIso (freeLightProfiniteMap S) := by
  erw [sequentialAdjunction.isIso_unit_app_iff_mem_essImage]
  exact ⟨_, ⟨(FreeImage.iso S).symm⟩⟩

end LightCondAb
