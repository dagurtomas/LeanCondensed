import Mathlib

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators

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
    change profiniteComponentMap S (pnatHomLeInt (𝟙 c)) = 𝟙 (profiniteComponent S c)
    trans profiniteComponentMap S (le_refl (c : ℤ))
    · apply profiniteComponentMap_congr
    · exact profiniteComponentMap_id S c
  map_comp := by
    intro c d e f g
    change profiniteComponentMap S (pnatHomLeInt (f ≫ g)) =
      profiniteComponentMap S (pnatHomLeInt f) ≫ profiniteComponentMap S (pnatHomLeInt g)
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

end FreeImage

end LightProfinite

namespace LightCondAb

variable (S : LightProfinite.{0})

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
