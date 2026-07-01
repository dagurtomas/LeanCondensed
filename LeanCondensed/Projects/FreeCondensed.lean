import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.Condensed.Discrete.Module
import Mathlib.Condensed.Light.Explicit
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.TopCatAdjunction
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Category.LightProfinite.AsLimit
import Mathlib.Topology.Category.Sequential
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators

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
