import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.Limits.FintypeCat
import LeanCondensed.LightProfinite.AsLimit
import LeanCondensed.LightProfinite.Reindex

noncomputable section

open CategoryTheory Limits Function Profinite FintypeCat

attribute [local instance] ConcreteCategory.instFunLike

namespace LightProfinite

variable (S : LightProfinite)

abbrev component (n : ℕ) : LightProfinite := S.diagram.obj ⟨n⟩

abbrev transitionMap (n : ℕ) :  S.component (n+1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

abbrev transitionMapLE {n m : ℕ} (h : n ≤ m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

@[simp, reassoc]
lemma proj_comp_transitionMap (n : ℕ) : S.proj (n + 1) ≫ S.transitionMap n = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

@[simp, reassoc]
lemma proj_comp_transitionMapLE {n m : ℕ} (h : n ≤ m) :
    S.proj m ≫ S.transitionMapLE h = S.proj n :=
  S.asLimitCone.w (homOfLE h).op

@[simp]
lemma proj_comp_transitionMapLE' {n m : ℕ} (h : n ≤ m) :
    S.transitionMapLE h ∘ S.proj m  = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

def homMk {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ (Y.component n))
    (w : ∀ n, Y.transitionMap n ∘ f (n + 1) = f n) : X ⟶ Y :=
  let c : Cone Y.diagram := ⟨X, natTrans_nat_op_mk f
    (by intro n; ext; exact congrFun (w n).symm _)⟩
  Y.asLimit.lift c

abbrev homMk'' {X Y : LightProfinite}
    (f : (n : ℕ) → X ⟶ Y.component n)
    (w : ∀ n, f (n + 1) ≫ Y.transitionMap n = f n) : X ⟶ Y :=
  homMk f fun n ↦ funext fun x ↦ DFunLike.ext_iff.mp (w n) x

theorem extracted_3 {X Y : LightProfinite}
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
  have : Y.proj n ∘ homMk f w = f n := extracted_3 f w n
  rw [← congrFun this a, ← congrFun this b]
  simp only [Function.comp_apply]
  erw [hab]

universe u

-- TODO: PR to `Basic`
instance {J : Type} [Category J] [CountableCategory J] :
    PreservesLimitsOfShape J (forget LightProfinite.{u}) :=
  have : PreservesLimitsOfSize.{0} (forget Profinite) := preservesLimitsOfSizeShrink _
  show PreservesLimitsOfShape J (lightToProfinite.{u} ⋙ forget Profinite) from inferInstance

theorem ext {Y : LightProfinite} {a b : Y} (h : ∀ n, Y.proj n a = Y.proj n b) : a = b := by
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
    have := congrFun (extracted_3 f w n) x
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
    erw [← congrFun (extracted_3 f w j) x, ← congrFun (extracted_3 f w i) x]
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
