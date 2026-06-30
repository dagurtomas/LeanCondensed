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

instance : IsIso (freeLightProfiniteMap S) := by
  erw [sequentialAdjunction.isIso_unit_app_iff_mem_essImage]
  exact ⟨_, ⟨(FreeImage.iso S).symm⟩⟩

end LightCondAb
