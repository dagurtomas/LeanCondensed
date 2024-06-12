/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.Topology.Category.LightProfinite.Basic
import LeanCondensed.NatFunctor
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

Further, we give a constructor `homMk` to define morphisms into a light profinite set by giving the
projections to the limit, and conditions for such maps to be injective/surjective.

Finally, we prove that this limit can be reindexed by a cofinal map `ℕ → ℕ` (see `reindex`-).

-/

noncomputable section

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {c c' : Cone F}

-- Is this really not in mathlib?
@[simps]
def CategoryTheory.Limits.Cones.ptIsoOfIso (i : c ≅ c') : c.pt ≅ c'.pt where
  hom := i.hom.hom
  inv := i.inv.hom
  hom_inv_id := by simp [← Cone.category_comp_hom]
  inv_hom_id := by simp [← Cone.category_comp_hom]

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

-- TODO: move and PR
instance : CountableCategory ℕ where

/-- The functor `ℕᵒᵖ ⥤ Fintype` whose limit is isomorphic to `X`. -/
abbrev fintypeDiagram : ℕᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram

/-- An abbreviation for `S.fintypeDiagram ⋙ FintypeCat.toProfinite`. -/
abbrev diagram : ℕᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
A cone over `S.diagram` whose cone point is isomorphic to `X`.
(Auxiliary definition, use `S.asLimitCone` instead.)
-/
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

/-- An auxiliary isomorphism of cones used to prove that `S.asLimitConeAux` is a limit cone. -/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

/--
`S.asLimitConeAux` is indeed a limit cone.
(Auxiliary definition, use `S.asLimit` instead.)
-/
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/-- A cone over `S.diagram` whose cone point is `X`. -/
def asLimitCone : Cone S.diagram where
  pt := S
  π := {
    app := fun n ↦ (lightToProfiniteFullyFaithful.preimageIso <|
      Cones.ptIsoOfIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ ↦ by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

/-- `S.asLimitCone` is indeed a limit cone. -/
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit <|
  Cones.ext (lightToProfiniteFullyFaithful.preimageIso <|
    Cones.ptIsoOfIso S.isoMapCone) (fun _ ↦ by rw [← @Iso.inv_comp_eq]; rfl)

/-- A bundled version of `S.asLimitCone` and `S.asLimit`. -/
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩

abbrev proj (n : ℕ) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩

lemma map_liftedLimit {C D J : Type*} [Category C] [Category D] [Category J] {K : J ⥤ C}
    {F : C ⥤ D} [CreatesLimit K F] {c : Cone (K ⋙ F)} (t : IsLimit c) (n : J) :
    (liftedLimitMapsToOriginal t).inv.hom ≫ F.map ((liftLimit t).π.app n) = c.π.app n := by
  have : (liftedLimitMapsToOriginal t).hom.hom ≫ c.π.app n = F.map ((liftLimit t).π.app n) := by
    simp
  rw [← this, ← Category.assoc, ← Cone.category_comp_hom]
  simp

lemma lightToProfinite_map_proj_eq (n : ℕ) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [Functor.comp_obj, proj, asLimitCone, Functor.const_obj_obj, asLimitConeAux, isoMapCone,
    Functor.FullyFaithful.preimageIso_inv, Cones.ptIsoOfIso_inv, Functor.map_comp,
    Functor.FullyFaithful.map_preimage]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact map_liftedLimit hc _

lemma proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩

abbrev transitionMap (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

@[simp, reassoc]
lemma proj_comp_transitionMap (n : ℕ) : S.proj (n + 1) ≫ S.transitionMap n = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

@[simp]
lemma proj_comp_transitionMap' (n : ℕ) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl

@[simp, reassoc]
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.transitionMapLE h = S.proj n :=
  S.asLimitCone.w (homOfLE h).op

@[simp]
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

lemma surjective_transitionMap (n : ℕ) : Function.Surjective (S.transitionMap n) := by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n

lemma surjective_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    Function.Surjective (S.transitionMapLE h) := by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

def homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  let c : Cone Y.diagram := ⟨X, natTrans_nat_op_mk f
    (by intro n; ext; exact congrFun (w n).symm _)⟩
  Y.asLimit.lift c

abbrev homMk' {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, f (n + 1) ≫ Y.transitionMap n = f n) : X ⟶ Y :=
  homMk f fun n ↦ funext fun x ↦ DFunLike.ext_iff.mp (w n) x

lemma proj_comp_homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) (n : ℕ) :
    (proj Y n) ∘ (homMk f w) = (f n) := by
  ext
  change (Y.asLimit.lift _ ≫ Y.asLimitCone.π.app _) _ = _
  simp only [Functor.comp_obj, IsLimit.fac]
  rfl

lemma homMk_injective {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n)
    (h : ∀ (a b : X), (∀ n, f n a = f n b) → a = b) : Function.Injective (homMk f w) := by
  intro a b hab
  apply h a b
  intro n
  have : Y.proj n ∘ homMk f w = f n := proj_comp_homMk f w n
  rw [← congrFun this a, ← congrFun this b]
  simp only [Function.comp_apply]
  erw [hab]

-- TODO: PR to `Basic`
instance {J : Type} [Category J] [CountableCategory J] :
    PreservesLimitsOfShape J (forget LightProfinite.{u}) :=
  have : PreservesLimitsOfSize.{0} (forget Profinite) := preservesLimitsOfSizeShrink _
  show PreservesLimitsOfShape J (lightToProfinite.{u} ⋙ forget Profinite) from inferInstance

lemma ext {Y : LightProfinite} {a b : Y} (h : ∀ n, Y.proj n a = Y.proj n b) : a = b := by
  exact Concrete.isLimit_ext _ Y.asLimit _ _ fun n ↦ h n.unop

lemma homMk_surjective {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n)
    (h : ∀ (a : Y) n, ∃ (b : X), f n b = Y.proj n a) : Function.Surjective (homMk f w) := by
  intro a
  replace h : ∀ n, Set.Nonempty ((f n) ⁻¹' {Y.proj n a}) := fun n ↦ h a n
  have := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ h ?_ ?_
  · obtain ⟨x, hx⟩ := this
    refine ⟨x, ?_⟩
    apply ext
    intro n
    have := congrFun (proj_comp_homMk f w n) x
    simp only [Function.comp_apply] at this
    erw [this]
    exact Set.mem_iInter.1 hx n
  · apply directed_of_isDirected_le
    intro i j hij x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    intro hx
    erw [← congrFun (Y.proj_comp_transitionMapLE' hij) a]
    simp only [Function.comp_apply]
    rw [← hx]
    erw [← congrFun (proj_comp_homMk f w j) x, ← congrFun (proj_comp_homMk f w i) x]
    simp only [Function.comp_apply]
    exact (congrFun (Y.proj_comp_transitionMapLE' hij) _).symm
  · exact fun i ↦ (IsClosed.preimage (f i).2 isClosed_singleton).isCompact
  · exact fun i ↦ IsClosed.preimage (f i).2 isClosed_singleton

def locallyConstant_of_hom {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    LocallyConstant X (Y.diagram.obj ⟨n⟩) where
  toFun x := Y.proj n (f x)
  isLocallyConstant := by
    let _ : TopologicalSpace (Y.diagram.obj ⟨n⟩) := ⊥
    have : DiscreteTopology (Y.diagram.obj ⟨n⟩) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact (f ≫ Y.proj n).continuous

def locallyConstant_of_hom_w {X Y : LightProfinite} (f : X ⟶ Y) (n : ℕ) :
    Y.transitionMap n ∘ locallyConstant_of_hom f (n + 1) = locallyConstant_of_hom f n := by
  change Y.transitionMap n ∘ (Y.proj _) ∘ f = _
  simp [← Function.comp.assoc]
  erw [← CategoryTheory.coe_comp, proj_comp_transitionMap]
  rfl

lemma eq_homMk {X Y : LightProfinite} (f : X ⟶ Y) :
    f = homMk (fun n ↦ (locallyConstant_of_hom f n).toContinuousMap)
      (locallyConstant_of_hom_w f) := by
  apply Y.asLimit.hom_ext
  intro ⟨n⟩
  ext
  simp only [Functor.comp_obj, CategoryTheory.comp_apply, homMk,
    locallyConstant_of_hom, LocallyConstant.coe_mk, IsLimit.fac]
  rfl

variable (X : LightProfinite.{u}) (f : ℕ → ℕ) (hf : Monotone f) (hf' : ∀ n, (∃ m, n ≤ f m))

noncomputable section

def reindexDiagram : ℕᵒᵖ ⥤ LightProfinite := (Nat.functor f hf).op ⋙ X.diagram

def reindexCone : Cone (X.reindexDiagram f hf) := X.asLimitCone.whisker (Nat.functor f hf).op

def reindexIsLimit : IsLimit (X.reindexCone f hf) :=
  ((initial f hf hf').isLimitWhiskerEquiv _).symm X.asLimit

example : X ≅ (X.reindexCone f hf).pt := Iso.refl _

variable {X}

def reindexHomMk {Y : LightProfinite} (g : (n : ℕ) → Y ⟶ X.component (f n))
    (w : ∀ n, X.transitionMapLE (hf (Nat.le_succ n)) ∘ g (n + 1) = g n) : Y ⟶ X :=
  let c : Cone (X.reindexDiagram f hf) := ⟨Y, natTrans_nat_op_mk g
    (by intro n; ext; exact congrFun (w n).symm _)⟩
  (X.reindexIsLimit f hf hf').lift c
