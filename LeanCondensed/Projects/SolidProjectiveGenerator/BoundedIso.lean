module

public import LeanCondensed.Projects.SolidProjectiveGenerator.ZdiscSeparation
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The bounded-sequence shift-retract data of Lemma 3.3.3. -/
noncomputable def boundedShiftRetractData :
    CategoryTheory.ShiftRetractData solidification where
  xObj := P ℤ ⊗ boundedIntSequences
  aObj := P ℤ
  bObj := boundedIntSequences
  s := (oneMinusShift ℤ) ▷ boundedIntSequences
  toB := boundedTailMap
  toA := boundedDifferenceMap
  g := basisMap
  comm := boundedShiftRetract_comm
  sect := boundedTailSection
  sect_fac := boundedTailSection_fac
  inverted := solidification_map_oneMinusShift_tensor_isIso boundedIntSequences

/-- The split-epimorphism retract obtained from the bounded shift-retract diagram. -/
noncomputable def solidifiedBoundedRetractSolidP :
    Retract (solidification.obj boundedIntSequences) solidP :=
  boundedShiftRetractData.retract

/-- Fallback `SPG9-retract-only`: the bounded diagram makes
`solidification.map basisMap` a split epimorphism. -/
lemma SPG9_retract_only :
    solidifiedBoundedRetractSolidP.i ≫ solidification.map basisMap =
      𝟙 (solidification.obj boundedIntSequences) := by
  change (boundedShiftRetractData.retract).i ≫ solidification.map basisMap =
    𝟙 (solidification.obj boundedIntSequences)
  change (boundedShiftRetractData.retract).i ≫ (boundedShiftRetractData.retract).r =
    𝟙 (solidification.obj boundedIntSequences)
  exact boundedShiftRetractData.retract.retract

/-- The pointwise truncation map `(n, k) ↦ k` for `n ≤ k`, and `∞` otherwise. -/
def pTailTruncFun
    (x : (((ℕ∪{∞} : LightProfinite) ⊗ (ℕ∪{∞} : LightProfinite)) : LightProfinite)) :
    (ℕ∪{∞} : LightProfinite) :=
  match x.1, x.2 with
  | ∞, _ => ∞
  | _, ∞ => ∞
  | OnePoint.some n, OnePoint.some k => if n ≤ k then (k : ℕ∪{∞}) else ∞

@[simp]
lemma pTailTruncFun_infty_left (b : (ℕ∪{∞} : LightProfinite)) :
    pTailTruncFun ((∞ : ℕ∪{∞}), b) = ∞ := rfl

@[simp]
lemma pTailTruncFun_infty_right (a : (ℕ∪{∞} : LightProfinite)) :
    pTailTruncFun (a, (∞ : ℕ∪{∞})) = ∞ := by
  cases a using OnePoint.rec <;> rfl

@[simp]
lemma pTailTruncFun_finite_finite (n k : ℕ) :
    pTailTruncFun ((n : ℕ∪{∞}), (k : ℕ∪{∞})) =
      if n ≤ k then (k : ℕ∪{∞}) else ∞ := rfl

lemma pTailTruncFun_preimage_finite (k : ℕ) :
    pTailTruncFun ⁻¹' ({(k : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)) =
      Set.prod ({a : (ℕ∪{∞} : LightProfinite) |
        ∃ n : ℕ, n ≤ k ∧ a = (n : ℕ∪{∞})})
        ({(k : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)) := by
  ext p
  rcases p with ⟨a, b⟩
  constructor
  · intro hp
    cases a using OnePoint.rec with
    | infty =>
        change (∞ : (ℕ∪{∞} : LightProfinite)) = (k : ℕ∪{∞}) at hp
        cases hp
    | coe n =>
        cases b using OnePoint.rec with
        | infty =>
            change (∞ : (ℕ∪{∞} : LightProfinite)) = (k : ℕ∪{∞}) at hp
            cases hp
        | coe l =>
            change (if n ≤ l then (l : ℕ∪{∞}) else ∞) = (k : ℕ∪{∞}) at hp
            by_cases hnl : n ≤ l
            · simp [hnl] at hp
              have hlk : l = k := by simpa using hp
              subst l
              exact ⟨⟨n, hnl, rfl⟩, rfl⟩
            · simp [hnl] at hp
  · intro hp
    rcases hp with ⟨ha, hb⟩
    rcases ha with ⟨n, hnle, rfl⟩
    simp at hb
    subst hb
    change (if n ≤ k then (k : ℕ∪{∞}) else ∞) = (k : ℕ∪{∞})
    simp [hnle]

lemma pTailTruncFun_fiber_finite (k : ℕ) :
    (pTailTruncFun ⁻¹' ({(k : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite))).Finite := by
  rw [pTailTruncFun_preimage_finite k]
  have hleft : ({a : (ℕ∪{∞} : LightProfinite) |
      ∃ n : ℕ, n ≤ k ∧ a = (n : ℕ∪{∞})}).Finite := by
    let s : Set ℕ := {n : ℕ | n ≤ k}
    have hs : s.Finite := Set.finite_le_nat k
    have himg : ((fun n : ℕ => (n : ℕ∪{∞})) '' s).Finite := hs.image _
    refine himg.subset ?_
    intro a ha
    rcases ha with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  have hright : ({(k : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)).Finite :=
    Set.finite_singleton _
  exact hleft.prod hright

lemma pTailTruncFun_fiber_open (k : ℕ) :
    IsOpen (pTailTruncFun ⁻¹' ({(k : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite))) := by
  rw [pTailTruncFun_preimage_finite k]
  apply IsOpen.prod
  · have hleft : {a : (ℕ∪{∞} : LightProfinite) |
        ∃ n : ℕ, n ≤ k ∧ a = (n : ℕ∪{∞})} =
        ⋃ n : {n : ℕ // n ≤ k}, ({(n.1 : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)) := by
      ext a
      constructor
      · intro ha
        rcases ha with ⟨n, hn, rfl⟩
        exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, rfl⟩
      · intro ha
        rcases Set.mem_iUnion.1 ha with ⟨n, hnmem⟩
        exact ⟨n.1, n.2, by simpa using hnmem⟩
    rw [hleft]
    apply isOpen_iUnion
    intro n
    simpa using finite_nat_singleton_open n.1
  · simpa using finite_nat_singleton_open k

lemma pTailTruncFun_continuous : Continuous pTailTruncFun := by
  rw [continuous_def]
  intro U hU
  by_cases hinfty : (∞ : (ℕ∪{∞} : LightProfinite)) ∈ U
  · have hcompact : IsCompact (OnePoint.some ⁻¹' U)ᶜ :=
      ((OnePoint.isOpen_iff_of_mem' hinfty).1 hU).1
    have hfinNat : ((OnePoint.some ⁻¹' U)ᶜ : Set ℕ).Finite := by
      simpa using (isCompact_iff_finite.mp hcompact)
    have hpre_subset : pTailTruncFun ⁻¹' Uᶜ ⊆
        ⋃ k : {k : ℕ // k ∈ (OnePoint.some ⁻¹' U)ᶜ},
          pTailTruncFun ⁻¹' ({(k.1 : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)) := by
      intro p hp
      have hout_ne : pTailTruncFun p ≠ (∞ : (ℕ∪{∞} : LightProfinite)) := by
        intro h
        exact hp (by simpa [h] using hinfty)
      cases hval : pTailTruncFun p using OnePoint.rec with
      | infty => exact False.elim (hout_ne hval)
      | coe k =>
          have hk : k ∈ (OnePoint.some ⁻¹' U)ᶜ := by
            change (k : ℕ∪{∞}) ∉ U
            intro hkU
            exact hp (by simpa [hval] using hkU)
          exact Set.mem_iUnion.2 ⟨⟨k, hk⟩, by simp [hval]⟩
    have hfinite_pre : (pTailTruncFun ⁻¹' Uᶜ).Finite := by
      letI : Fintype {k : ℕ // k ∈ (OnePoint.some ⁻¹' U)ᶜ} := hfinNat.fintype
      exact (Set.finite_iUnion (fun k : {k : ℕ // k ∈ (OnePoint.some ⁻¹' U)ᶜ} =>
        pTailTruncFun_fiber_finite k.1)).subset hpre_subset
    have hclosed : IsClosed (pTailTruncFun ⁻¹' Uᶜ) := hfinite_pre.isClosed
    simpa [Set.preimage_compl] using hclosed.isOpen_compl
  · have hpre_eq : pTailTruncFun ⁻¹' U =
        ⋃ k : {k : ℕ // (k : ℕ∪{∞}) ∈ U},
          pTailTruncFun ⁻¹' ({(k.1 : ℕ∪{∞})} : Set (ℕ∪{∞} : LightProfinite)) := by
      ext p
      constructor
      · intro hp
        cases hval : pTailTruncFun p using OnePoint.rec with
        | infty => exact False.elim (hinfty (by simpa [hval] using hp))
        | coe k =>
            exact Set.mem_iUnion.2 ⟨⟨k, by simpa [hval] using hp⟩, by simp [hval]⟩
      · intro hp
        rcases Set.mem_iUnion.1 hp with ⟨k, hk⟩
        have hout : pTailTruncFun p = (k.1 : ℕ∪{∞}) := by simpa using hk
        change pTailTruncFun p ∈ U
        rw [hout]
        exact k.2
    rw [hpre_eq]
    apply isOpen_iUnion
    intro k
    exact pTailTruncFun_fiber_open k.1

/-- The truncation map on `(ℕ∪∞) × (ℕ∪∞)` used for the self-diagram on `P ℤ`. -/
noncomputable def pTailTruncMap :
    (((ℕ∪{∞} : LightProfinite) ⊗ (ℕ∪{∞} : LightProfinite)) : LightProfinite) ⟶
      (ℕ∪{∞} : LightProfinite) :=
  ConcreteCategory.ofHom ⟨pTailTruncFun, pTailTruncFun_continuous⟩

@[simp]
lemma pTailTruncMap_apply (a b : (ℕ∪{∞} : LightProfinite)) :
    pTailTruncMap (a, b) = pTailTruncFun (a, b) := rfl

lemma pTailTruncMap_right_infty :
    ((ℕ∪{∞} : LightProfinite) ◁ ι) ≫ pTailTruncMap =
      toPointMap (((ℕ∪{∞} : LightProfinite) ⊗ LightProfinite.of PUnit.{1}) : LightProfinite) ≫ ι := by
  ext x
  rcases x with ⟨a, u⟩
  cases a using OnePoint.rec <;> rfl

lemma pTailTruncMap_left_infty :
    (ι ▷ (ℕ∪{∞} : LightProfinite)) ≫ pTailTruncMap =
      toPointMap ((LightProfinite.of PUnit.{1} ⊗ (ℕ∪{∞} : LightProfinite)) : LightProfinite) ≫ ι := by
  ext x
  rcases x with ⟨u, a⟩
  rfl

lemma free_constInfty_comp_P_proj (T : LightProfinite) :
    (free ℤ).map (lightProfiniteToLightCondSet.map (toPointMap T ≫ ι)) ≫ P_proj ℤ = 0 := by
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

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
lemma freeTensorHomPresheafComposite_comp (X : LightProfinite.{0}) (B C D : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C) (h : C ⟶ D) :
    freeTensorHomPresheafComposite X B D (g ≫ h) =
      freeTensorHomPresheafComposite X B C g ≫ h.hom := by
  dsimp [freeTensorHomPresheafComposite]
  simp [Category.assoc]

lemma freeTensorHomEval_comp (X : LightProfinite.{0}) (B C D : LightCondAb)
    (g : ((free ℤ).obj X.toCondensed) ⊗ B ⟶ C) (h : C ⟶ D)
    (S : LightProfinite.{0}) (f : S ⟶ X) (r : ℤ) (m : B.obj.obj ⟨S⟩) :
    freeTensorHomEval X B D (g ≫ h) S f r m =
      h.hom.app ⟨S⟩ (freeTensorHomEval X B C g S f r m) := by
  dsimp [freeTensorHomEval]
  rw [freeTensorHomPresheafComposite_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_naturality_right {A S' S : LightProfinite} (φ : S' ⟶ S) :
    (((free ℤ).obj A.toCondensed) ◁ (free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫
        (IntProof.freeTensorIsoInt A S).hom =
      (IntProof.freeTensorIsoInt A S').hom ≫
        (free ℤ).map (lightProfiniteToLightCondSet.map (𝟙 A ⊗ₘ φ)) := by
  dsimp [IntProof.freeTensorIsoInt]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc (free ℤ)
    A.toCondensed (lightProfiniteToLightCondSet.map φ)
    ((free ℤ).map (Functor.LaxMonoidal.μ lightProfiniteToLightCondSet A S))]
  slice_lhs 2 4 => rw [← Functor.map_comp]
  slice_rhs 2 4 => rw [← Functor.map_comp]
  rw [Functor.LaxMonoidal.μ_natural_right lightProfiniteToLightCondSet]
  simp [MonoidalCategory.id_tensorHom]

/-- The free-valued lift of the free-free tail numerator induced by the truncation map. -/
noncomputable def pTailFreeFreeLift :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗
      ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⟶
        (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  (IntProof.freeTensorIsoInt (ℕ∪{∞} : LightProfinite) (ℕ∪{∞} : LightProfinite)).hom ≫
    (free ℤ).map (lightProfiniteToLightCondSet.map pTailTruncMap)

/-- The free-free numerator induced by the truncation map. -/
noncomputable def pTailFreeFree :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⟶ P ℤ :=
  pTailFreeFreeLift ≫ P_proj ℤ

lemma pTailFreeFree_kills_right :
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_map ℤ) ≫ pTailFreeFree = 0 := by
  dsimp [pTailFreeFree, pTailFreeFreeLift, P_map]
  simp only [Category.assoc]
  rw [freeTensorIsoInt_hom_naturality_right_assoc (φ := ι)]
  slice_lhs 2 3 => rw [← Functor.map_comp]
  simp only [MonoidalCategory.id_tensorHom]
  rw [← Functor.map_comp]
  rw [pTailTruncMap_right_infty]
  rw [free_constInfty_comp_P_proj]
  simp

lemma pTailFreeFree_kills_left :
    (P_map ℤ ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed)) ≫ pTailFreeFree = 0 := by
  dsimp [pTailFreeFree, pTailFreeFreeLift, P_map]
  simp only [Category.assoc]
  rw [freeTensorIsoInt_hom_naturality_left_assoc (φ := ι)]
  slice_lhs 2 3 => rw [← Functor.map_comp]
  simp only [MonoidalCategory.tensorHom_id]
  rw [← Functor.map_comp]
  rw [pTailTruncMap_left_infty]
  rw [free_constInfty_comp_P_proj]
  simp

/-- Descend a map out of `M ⊗ ℤ[ℕ∪∞]` through the quotient in the right tensor factor. -/
noncomputable def pTensorDescRight (M N : LightCondAb)
    (f : M ⊗ ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⟶ N)
    (hf : (M ◁ P_map ℤ) ≫ f = 0) : M ⊗ P ℤ ⟶ N :=
  (β_ M (P ℤ)).hom ≫
    pTensorDesc M N ((β_ ((free ℤ).obj (ℕ∪{∞}).toCondensed) M).hom ≫ f) (by
      rw [BraidedCategory.braiding_naturality_left_assoc]
      rw [hf]
      simp)

@[reassoc]
lemma pTensorDescRight_comp_proj (M N : LightCondAb)
    (f : M ⊗ ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⟶ N)
    (hf : (M ◁ P_map ℤ) ≫ f = 0) :
    (M ◁ P_proj ℤ) ≫ pTensorDescRight M N f hf = f := by
  dsimp [pTensorDescRight]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [pTensorDesc_comp_proj]
  simp

/-- The numerator `ℤ[ℕ∪∞] ⊗ P ℤ ⟶ P ℤ` for the self-tail map. -/
noncomputable def pTailNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ P ℤ ⟶ P ℤ :=
  pTensorDescRight ((free ℤ).obj (ℕ∪{∞}).toCondensed) (P ℤ)
    pTailFreeFree pTailFreeFree_kills_right

lemma pTailNumerator_kills :
    (P_map ℤ ▷ P ℤ) ≫ pTailNumerator = 0 := by
  let freePointObj : LightCondAb := (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed
  let freeNinfObj : LightCondAb := (free ℤ).obj (ℕ∪{∞}).toCondensed
  let e : freePointObj ⊗ freeNinfObj ⟶ freePointObj ⊗ P ℤ :=
    (β_ freePointObj freeNinfObj).hom ≫ (P_proj ℤ ▷ freePointObj) ≫
      (β_ (P ℤ) freePointObj).hom
  have he : e = freePointObj ◁ (P_proj ℤ) := by
    apply (cancel_mono (β_ freePointObj (P ℤ)).hom).1
    dsimp [e, freeNinfObj]
    rw [Category.assoc]
    rw [BraidedCategory.braiding_naturality_right]
    simp
  haveI : Epi (P_proj ℤ ▷ freePointObj) := epi_P_proj_tensor freePointObj
  haveI : Epi e := by dsimp [e]; infer_instance
  haveI : Epi (freePointObj ◁ (P_proj ℤ)) := by
    rw [← he]
    infer_instance
  apply (cancel_epi (freePointObj ◁ (P_proj ℤ))).1
  calc
    (freePointObj ◁ (P_proj ℤ)) ≫ ((P_map ℤ ▷ P ℤ) ≫ pTailNumerator)
        = (P_map ℤ ▷ freeNinfObj) ≫ ((freeNinfObj ◁ P_proj ℤ) ≫ pTailNumerator) := by
          dsimp [freeNinfObj]
          rw [← Category.assoc]
          rw [whisker_exchange]
          simp [Category.assoc]
    _ = (P_map ℤ ▷ freeNinfObj) ≫ pTailFreeFree := by
          dsimp [pTailNumerator, freeNinfObj]
          rw [pTensorDescRight_comp_proj]
    _ = 0 := by
          rw [pTailFreeFree_kills_left]

/-- In-place truncation endomorphism of `P ℤ`: finite basis vector `k` is kept iff `n ≤ k`. -/
noncomputable def pTailProjectionPointMap (n : ℕ) :
    (ℕ∪{∞} : LightProfinite) ⟶ (ℕ∪{∞} : LightProfinite) :=
  finiteTensorPoint (ℕ∪{∞} : LightProfinite) n ≫ pTailTruncMap

lemma pTailProjectionPointMap_infty (n : ℕ) :
    ι ≫ pTailProjectionPointMap n = toPointMap (LightProfinite.of PUnit.{1}) ≫ ι := by
  ext u
  change (∞ : ℕ∪{∞}) = (∞ : ℕ∪{∞})
  rfl

noncomputable def pTailProjectionNumerator (n : ℕ) :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ P ℤ :=
  (free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap n)) ≫ P_proj ℤ

lemma pTailFreeFreeLift_slice (n : ℕ) :
    numeratorSlice ((free ℤ).obj (ℕ∪{∞}).toCondensed)
      ((free ℤ).obj (ℕ∪{∞}).toCondensed) n pTailFreeFreeLift =
      (free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap n)) := by
  dsimp [numeratorSlice, pTailFreeFreeLift, pTailProjectionPointMap]
  rw [freeTensorIsoInt_hom_finiteTensorPoint_assoc]
  rw [← Functor.map_comp]
  rfl

lemma pTailProjectionNumerator_kills (n : ℕ) :
    P_map ℤ ≫ pTailProjectionNumerator n = 0 := by
  dsimp [pTailProjectionNumerator, P_map]
  rw [← Category.assoc]
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [pTailProjectionPointMap_infty]
  exact free_constInfty_comp_P_proj (LightProfinite.of PUnit.{1})

noncomputable def pTailProjection (n : ℕ) : P ℤ ⟶ P ℤ :=
  P_homMk ℤ (P ℤ) (pTailProjectionNumerator n) (pTailProjectionNumerator_kills n)

@[reassoc]
lemma P_proj_comp_pTailProjection (n : ℕ) :
    P_proj ℤ ≫ pTailProjection n = pTailProjectionNumerator n := by
  change cokernel.π (P_map ℤ) ≫ cokernel.desc (P_map ℤ) (pTailProjectionNumerator n) _ = _
  exact cokernel.π_desc (P_map ℤ) (pTailProjectionNumerator n) _

lemma pTailProjection_zero : pTailProjection 0 = 𝟙 (P ℤ) := by
  haveI : Epi (P_proj ℤ) := by
    change Epi (cokernel.π (P_map ℤ))
    infer_instance
  apply (cancel_epi (P_proj ℤ)).1
  rw [P_proj_comp_pTailProjection]
  dsimp [pTailProjectionNumerator, pTailProjectionPointMap]
  have hmap : finiteTensorPoint (ℕ∪{∞} : LightProfinite) 0 ≫ pTailTruncMap =
      𝟙 (ℕ∪{∞} : LightProfinite) := by
    ext a
    change pTailTruncMap (((0 : ℕ) : ℕ∪{∞}), a) = a
    rw [pTailTruncMap_apply]
    cases a using OnePoint.rec with
    | infty => rfl
    | coe k =>
        change (if 0 ≤ k then (k : ℕ∪{∞}) else ∞) = (k : ℕ∪{∞})
        simp
  rw [hmap]
  simp

lemma pTailFreeFree_slice (n : ℕ) :
    numeratorSlice ((free ℤ).obj (ℕ∪{∞}).toCondensed) (P ℤ) n pTailFreeFree =
      pTailProjectionNumerator n := by
  dsimp [numeratorSlice, pTailFreeFree, pTailFreeFreeLift, pTailProjectionNumerator, pTailProjectionPointMap]
  simp only [Category.assoc]
  rw [freeTensorIsoInt_hom_finiteTensorPoint_assoc]
  simp

lemma pTailNumerator_slice (n : ℕ) :
    numeratorSlice (P ℤ) (P ℤ) n pTailNumerator = pTailProjection n := by
  haveI : Epi (P_proj ℤ) := by
    change Epi (cokernel.π (P_map ℤ))
    infer_instance
  apply (cancel_epi (P_proj ℤ)).1
  rw [P_proj_comp_pTailProjection]
  dsimp [numeratorSlice]
  calc
    P_proj ℤ ≫ (λ_ (P ℤ)).inv ≫ freeNatBasis n ▷ P ℤ ≫ pTailNumerator
        = (λ_ ((free ℤ).obj (ℕ∪{∞}).toCondensed)).inv ≫
            freeNatBasis n ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed) ≫
              (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) ≫ pTailNumerator := by
          rw [leftUnitor_inv_naturality_assoc]
          rw [whisker_exchange_assoc]
    _ = (λ_ ((free ℤ).obj (ℕ∪{∞}).toCondensed)).inv ≫
          freeNatBasis n ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed) ≫ pTailFreeFree := by
          dsimp [pTailNumerator]
          rw [pTensorDescRight_comp_proj]
    _ = pTailProjectionNumerator n := pTailFreeFree_slice n

/-- The self-tail map `P ℤ ⊗ P ℤ ⟶ P ℤ`. -/
noncomputable def pTailMap : P ℤ ⊗ P ℤ ⟶ P ℤ :=
  pTensorDesc (P ℤ) (P ℤ) pTailNumerator pTailNumerator_kills

lemma pTailMap_slice (n : ℕ) :
    ((λ_ (P ℤ)).inv ≫ pBasis n ▷ P ℤ) ≫ pTailMap = pTailProjection n := by
  dsimp [pTailMap]
  rw [pTensorDesc_slice]
  exact pTailNumerator_slice n

/-- The zeroth self-tail section. -/
noncomputable def pTailSection : P ℤ ⟶ P ℤ ⊗ P ℤ :=
  (λ_ (P ℤ)).inv ≫ pBasis 0 ▷ P ℤ

lemma pTailSection_fac : pTailSection ≫ pTailMap = 𝟙 (P ℤ) := by
  rw [pTailSection, pTailMap_slice]
  exact pTailProjection_zero

/-- The P-level difference map, defined as tail after `1 - shift` in the first factor. -/
noncomputable def pDifferenceMap : P ℤ ⊗ P ℤ ⟶ P ℤ :=
  (oneMinusShift ℤ ▷ P ℤ) ≫ pTailMap

lemma pDifferenceMap_def :
    pDifferenceMap = (oneMinusShift ℤ ▷ P ℤ) ≫ pTailMap := rfl

@[reassoc]
lemma numeratorSlice_whiskerRight (M M' N : LightCondAb) (n : ℕ)
    (h : M' ⟶ M)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    numeratorSlice M' N n ((((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ h) ≫ f) =
      h ≫ numeratorSlice M N n f := by
  dsimp [numeratorSlice]
  rw [leftUnitor_inv_naturality_assoc h]
  slice_lhs 2 3 => rw [← whisker_exchange]
  simp [Category.assoc]

@[reassoc]
lemma inftySlice_whiskerRight (M M' N : LightCondAb)
    (h : M' ⟶ M)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    inftySlice M' N ((((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ h) ≫ f) =
      h ≫ inftySlice M N f := by
  dsimp [inftySlice]
  rw [leftUnitor_inv_naturality_assoc h]
  slice_lhs 2 3 => rw [← whisker_exchange]
  simp [Category.assoc]

/-- The free section lifting the bounded diagonal-difference family before quotienting by
`δ_∞`. -/
noncomputable def boundedDifferenceFreeSection {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.obj ⟨S⟩ :=
  (LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).symm.hom.hom.app ⟨S⟩
    (boundedDifferenceTopologicalSection f x)

lemma boundedDifferenceFreeSection_add {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x y : BoundedIntSeqSection S) :
    boundedDifferenceFreeSection f (x + y) =
      boundedDifferenceFreeSection f x + boundedDifferenceFreeSection f y := by
  dsimp [boundedDifferenceFreeSection]
  rw [boundedDifferenceTopologicalSection_add]
  exact ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom.map_add _ _

lemma boundedDifferenceFreeSection_zsmul {S : LightProfinite}
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (a : ℤ) (x : BoundedIntSeqSection S) :
    boundedDifferenceFreeSection f (a • x) = a • boundedDifferenceFreeSection f x := by
  dsimp [boundedDifferenceFreeSection]
  rw [boundedDifferenceTopologicalSection_zsmul]
  exact map_zsmul
    (((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩).hom) a _

lemma boundedDifferenceFreeSection_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite)) (x : BoundedIntSeqSection S) :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.map g.op (boundedDifferenceFreeSection f x) =
      boundedDifferenceFreeSection (g ≫ f) (boundedIntSeqSectionComap g x) := by
  dsimp [boundedDifferenceFreeSection]
  rw [← LightCondMod.hom_naturality_apply ℤ
    (LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv g.op]
  rw [boundedDifferenceTopologicalSection_naturality]

/-- The free-valued sectionwise linear family lifting `boundedDifferenceFamilyLinear`. -/
noncomputable def boundedDifferenceFreeFamilyLinear (S : LightProfinite)
    (f : S ⟶ (ℕ∪{∞} : LightProfinite)) :
    boundedIntSequences.obj.obj ⟨S⟩ →ₗ[ℤ]
      ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.obj ⟨S⟩ where
  toFun x := boundedDifferenceFreeSection f (show BoundedIntSeqSection S from x)
  map_add' := by
    intro x y
    exact boundedDifferenceFreeSection_add f (show BoundedIntSeqSection S from x)
      (show BoundedIntSeqSection S from y)
  map_smul' := by
    intro a x
    have hx : (show BoundedIntSeqSection S from a • x) =
        a • (show BoundedIntSeqSection S from x) := by
      apply BoundedIntSeqSection.ext_apply
      intro n s
      rfl
    convert boundedDifferenceFreeSection_zsmul f a (show BoundedIntSeqSection S from x) using 1
    · exact congrArg (boundedDifferenceFreeSection f) hx
    · simpa [RingHom.id_apply] using
        (Int.cast_smul_eq_zsmul (R := ℤ) a
          (boundedDifferenceFreeSection f (show BoundedIntSeqSection S from x)))

lemma boundedDifferenceFreeFamilyLinear_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : boundedIntSequences.obj.obj ⟨S⟩) :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.map g.op
        (boundedDifferenceFreeFamilyLinear S f m) =
      boundedDifferenceFreeFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  exact boundedDifferenceFreeSection_naturality g f (show BoundedIntSeqSection S from m)

lemma boundedDifferenceFreeFamilyLinear_naturality' :
    ∀ {S T : LightProfinite} (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
      (m : boundedIntSequences.obj.obj ⟨S⟩),
      ((free ℤ).obj (ℕ∪{∞}).toCondensed).obj.map g.op
          (boundedDifferenceFreeFamilyLinear S f m) =
        boundedDifferenceFreeFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  intro S T g f m
  exact boundedDifferenceFreeFamilyLinear_naturality g f m

/-- The free-valued numerator lifting the bounded diagonal-difference numerator. -/
noncomputable def boundedDifferenceFreeNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ boundedIntSequences ⟶
      (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  freeTensorDescLin (ℕ∪{∞} : LightProfinite) boundedIntSequences
    ((free ℤ).obj (ℕ∪{∞}).toCondensed)
    boundedDifferenceFreeFamilyLinear boundedDifferenceFreeFamilyLinear_naturality'

lemma boundedDifferenceFreeNumerator_slice (n : ℕ) :
    numeratorSlice boundedIntSequences ((free ℤ).obj (ℕ∪{∞}).toCondensed) n
      boundedDifferenceFreeNumerator =
      freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences
        ((free ℤ).obj (ℕ∪{∞}).toCondensed)
        boundedDifferenceFreeFamilyLinear boundedDifferenceFreeFamilyLinear_naturality'
        (natPoint n) := by
  dsimp [numeratorSlice, freeNatBasis, boundedDifferenceFreeNumerator]
  rw [freeTensorDescLin_point]

lemma boundedDifferenceFreeFamilyMap_infty :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences
      ((free ℤ).obj (ℕ∪{∞}).toCondensed)
      boundedDifferenceFreeFamilyLinear boundedDifferenceFreeFamilyLinear_naturality' ι =
    0 := by
  ext S x
  change boundedDifferenceFreeFamilyLinear S.unop (toPointMap S.unop ≫ ι) x =
    (0 : boundedIntSequences ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed).hom.app S x
  dsimp [boundedDifferenceFreeFamilyLinear, boundedDifferenceFreeSection]
  have htop : boundedDifferenceTopologicalSection (toPointMap S.unop ≫ ι)
      (show BoundedIntSeqSection S.unop from x) = 0 := by
    apply ContinuousMap.ext
    intro s
    change boundedDifferenceMeasure (toPointMap S.unop ≫ ι)
        (show BoundedIntSeqSection S.unop from x) s = 0
    dsimp [boundedDifferenceMeasure, boundedDifferenceCoeff]
    have hf : (ConcreteCategory.hom (toPointMap S.unop ≫ ι)) s =
        (∞ : ℕ∪{∞}) := rfl
    rw [hf]
    rw [topologicalFreeDiracDiff_self]
    change (0 : ℤ) • (0 : LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)) = 0
    exact zero_smul ℤ (0 : LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite))
  rw [htop]
  simp

lemma boundedDifferenceFreeNumerator_infty :
    inftySlice boundedIntSequences ((free ℤ).obj (ℕ∪{∞}).toCondensed)
      boundedDifferenceFreeNumerator = 0 := by
  dsimp [inftySlice, freeInftyBasis, P_map, boundedDifferenceFreeNumerator]
  rw [freeTensorDescLin_point]
  exact boundedDifferenceFreeFamilyMap_infty

lemma boundedDifferenceFreeNumerator_comp_P_proj :
    boundedDifferenceFreeNumerator ≫ P_proj ℤ = boundedDifferenceNumerator := by
  apply freeTensorHom_ext
  intro S f r m
  rw [freeTensorHomEval_comp]
  dsimp [boundedDifferenceFreeNumerator, boundedDifferenceNumerator]
  rw [freeTensorHomEval_desc]
  rw [freeTensorHomEval_desc]
  dsimp [boundedDifferenceFreeFamilyLinear, boundedDifferenceFamilyLinear,
    boundedDifferenceFreeSection, boundedDifferencePSection]
  change (P_proj ℤ).hom.app ⟨S⟩
      (r • ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩
        (boundedDifferenceTopologicalSection f (show BoundedIntSeqSection S from m)))) =
    r • (P_proj ℤ).hom.app ⟨S⟩
      ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).inv.hom.app ⟨S⟩
        (boundedDifferenceTopologicalSection f (show BoundedIntSeqSection S from m)))
  exact map_zsmul ((P_proj ℤ).hom.app ⟨S⟩).hom r _

lemma basisMapNumerator_comp_boundedDifferenceFreeFamilyMap_natPoint (n : ℕ) :
    basisMapNumerator ≫
      freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences
        ((free ℤ).obj (ℕ∪{∞}).toCondensed)
        boundedDifferenceFreeFamilyLinear boundedDifferenceFreeFamilyLinear_naturality'
        (natPoint n) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap n)) -
        (free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap (n + 1))) := by
  apply (freeHomEquivPoints (ℕ∪{∞} : LightProfinite)
    ((free ℤ).obj (ℕ∪{∞}).toCondensed)).injective
  apply LightCondAb.freeSection_map_eq_of_pointwise_measure_eq
    (ℕ∪{∞} : LightProfinite) (ℕ∪{∞} : LightProfinite)
  intro t
  rw [freeHomEquivPoints_comp]
  rw [freeHomEquivPoints_sub]
  dsimp [freeTensorFamilyMap, boundedDifferenceFreeFamilyLinear, basisMapNumerator]
  rw [Equiv.apply_symm_apply]
  dsimp [boundedDifferenceFreeSection]
  change (show C(↑(ℕ∪{∞} : LightProfinite).toTop,
      ↑(LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)).toModuleCat) from
      (LightCondAb.freeToTopologicalFree (ℕ∪{∞} : LightProfinite)).hom.app
        ⟨(ℕ∪{∞} : LightProfinite)⟩
        ((LightCondAb.freeTopologicalFreeIso (ℕ∪{∞} : LightProfinite)).symm.hom.hom.app
          ⟨(ℕ∪{∞} : LightProfinite)⟩
          (boundedDifferenceTopologicalSection (toPointMap (ℕ∪{∞} : LightProfinite) ≫ natPoint n)
            ((boundedIntSequencesSectionsEquiv (ℕ∪{∞} : LightProfinite)).symm
              boundedStandardBasisSection)))) t = _
  rw [LightCondAb.freeToTopologicalFree_app_section_of_iso_symm]
  rw [map_sub]
  change (show C(↑(ℕ∪{∞} : LightProfinite).toTop,
        ↑(LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)).toModuleCat) from
        boundedDifferenceTopologicalSection (toPointMap (ℕ∪{∞} : LightProfinite) ≫ natPoint n)
          ((boundedIntSequencesSectionsEquiv (ℕ∪{∞} : LightProfinite)).symm
            boundedStandardBasisSection)) t =
      (show C(↑(ℕ∪{∞} : LightProfinite).toTop,
        ↑(LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)).toModuleCat) from
        (LightCondAb.freeToTopologicalFree (ℕ∪{∞} : LightProfinite)).hom.app
          ⟨(ℕ∪{∞} : LightProfinite)⟩
          (freeHomEquivPoints (ℕ∪{∞} : LightProfinite) ((free ℤ).obj (ℕ∪{∞}).toCondensed)
            ((free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap n))))) t -
      (show C(↑(ℕ∪{∞} : LightProfinite).toTop,
        ↑(LightCondAb.topologicalFree (ℕ∪{∞} : LightProfinite)).toModuleCat) from
        (LightCondAb.freeToTopologicalFree (ℕ∪{∞} : LightProfinite)).hom.app
          ⟨(ℕ∪{∞} : LightProfinite)⟩
          (freeHomEquivPoints (ℕ∪{∞} : LightProfinite) ((free ℤ).obj (ℕ∪{∞}).toCondensed)
            ((free ℤ).map (lightProfiniteToLightCondSet.map (pTailProjectionPointMap (n + 1)))))) t
  rw [freeMap_topologicalFree_apply, freeMap_topologicalFree_apply]
  change boundedDifferenceMeasure (toPointMap (ℕ∪{∞} : LightProfinite) ≫ natPoint n)
      boundedStandardBasisSection t =
    Finsupp.single ((ConcreteCategory.hom (pTailProjectionPointMap n)) t) 1 -
      Finsupp.single ((ConcreteCategory.hom (pTailProjectionPointMap (n + 1))) t) 1
  cases t using OnePoint.rec with
  | infty =>
      change boundedDifferenceMeasure (toPointMap (ℕ∪{∞} : LightProfinite) ≫ natPoint n)
          boundedStandardBasisSection (∞ : (ℕ∪{∞} : LightProfinite)) =
        Finsupp.single (pTailTruncFun (((n : ℕ) : ℕ∪{∞}), (∞ : ℕ∪{∞}))) 1 -
          Finsupp.single (pTailTruncFun ((((n + 1 : ℕ) : ℕ∪{∞})), (∞ : ℕ∪{∞}))) 1
      simp [boundedDifferenceMeasure, boundedDifferenceCoeff, boundedStandardBasisSection,
        boundedStandardBasisCoord, topologicalFreeDiracDiff, toPointMap, natPoint, pTailTruncFun]
      abel
  | coe k =>
      change boundedDifferenceMeasure (toPointMap (ℕ∪{∞} : LightProfinite) ≫ natPoint n)
          boundedStandardBasisSection (k : (ℕ∪{∞} : LightProfinite)) =
        Finsupp.single (pTailTruncFun (((n : ℕ) : ℕ∪{∞}), ((k : ℕ) : ℕ∪{∞}))) 1 -
          Finsupp.single (pTailTruncFun ((((n + 1 : ℕ) : ℕ∪{∞})), ((k : ℕ) : ℕ∪{∞}))) 1
      by_cases hnk : n = k
      · subst k
        simp [boundedDifferenceMeasure, boundedDifferenceCoeff, boundedStandardBasisSection,
          boundedStandardBasisCoord, topologicalFreeDiracDiff, toPointMap, natPoint, pTailTruncFun]
        rfl
      · have hkn : k ≠ n := fun hk => hnk hk.symm
        by_cases hlt : n < k
        · have hnle : n ≤ k := Nat.le_of_lt hlt
          have hsucc : n + 1 ≤ k := by omega
          simp [boundedDifferenceMeasure, boundedDifferenceCoeff, boundedStandardBasisSection,
            boundedStandardBasisCoord, topologicalFreeDiracDiff, toPointMap, natPoint, pTailTruncFun,
            hkn, hnle, hsucc]
          abel
        · have hnle : ¬ n ≤ k := by omega
          have hsucc : ¬ n + 1 ≤ k := by omega
          simp [boundedDifferenceMeasure, boundedDifferenceCoeff, boundedStandardBasisSection,
            boundedStandardBasisCoord, topologicalFreeDiracDiff, toPointMap, natPoint, pTailTruncFun,
            hkn, hnle, hsucc]
          abel

lemma boundedDifferenceFreeNumerator_basisMapNumerator :
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ basisMapNumerator) ≫
        boundedDifferenceFreeNumerator =
      (oneMinusShift' ℤ ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed)) ≫ pTailFreeFreeLift := by
  apply freeTarget_numerator_ext_of_slices (ℕ∪{∞} : LightProfinite)
  · intro n
    rw [numeratorSlice_whiskerRight]
    rw [boundedDifferenceFreeNumerator_slice]
    rw [basisMapNumerator_comp_boundedDifferenceFreeFamilyMap_natPoint n]
    rw [numeratorSlice_oneMinusShift']
    rw [pTailFreeFreeLift_slice]
    rw [pTailFreeFreeLift_slice]
  · rw [inftySlice_whiskerRight]
    rw [boundedDifferenceFreeNumerator_infty]
    rw [inftySlice_oneMinusShift']
    simp

lemma epi_tensor_P_proj (M : LightCondAb) : Epi (M ◁ P_proj ℤ) := by
  let freeNinfObj : LightCondAb := (free ℤ).obj (ℕ∪{∞}).toCondensed
  let e : M ⊗ freeNinfObj ⟶ M ⊗ P ℤ :=
    (β_ M freeNinfObj).hom ≫ (P_proj ℤ ▷ M) ≫ (β_ (P ℤ) M).hom
  have he : e = M ◁ (P_proj ℤ) := by
    apply (cancel_mono (β_ M (P ℤ)).hom).1
    dsimp [e, freeNinfObj]
    rw [Category.assoc]
    rw [BraidedCategory.braiding_naturality_right]
    simp
  haveI : Epi (P_proj ℤ ▷ M) := epi_P_proj_tensor M
  haveI : Epi e := by dsimp [e]; infer_instance
  rw [← he]
  infer_instance

lemma freeFreeBasisMap_square :
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) ≫
      (P_proj ℤ ▷ P ℤ) ≫ (P ℤ ◁ basisMap) =
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ basisMapNumerator) ≫
      (P_proj ℤ ▷ boundedIntSequences) := by
  rw [← Category.assoc]
  rw [whisker_exchange]
  rw [Category.assoc]
  rw [← whiskerLeft_comp]
  rw [P_proj_comp_basisMap]
  rw [whisker_exchange]

lemma pDifferenceMap_freeFree_lift :
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) ≫
      (P_proj ℤ ▷ P ℤ) ≫ pDifferenceMap =
    (oneMinusShift' ℤ ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed)) ≫
      pTailFreeFreeLift ≫ P_proj ℤ := by
  dsimp [pDifferenceMap, pTailMap]
  slice_lhs 2 3 => rw [P_proj_tensor_oneMinusShift]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 3 4 => rw [pTensorDesc_comp_proj]
  dsimp [pTailNumerator]
  slice_lhs 2 3 => rw [pTensorDescRight_comp_proj]
  dsimp [pTailFreeFree]

/-- Compatibility of the bounded diagonal-difference map with the standard-basis copy of `P ℤ`. -/
lemma pDifferenceMap_compat :
    (P ℤ ◁ basisMap) ≫ boundedDifferenceMap = pDifferenceMap := by
  haveI : Epi (P_proj ℤ ▷ P ℤ) := epi_P_proj_tensor (P ℤ)
  apply (cancel_epi (P_proj ℤ ▷ P ℤ)).1
  haveI : Epi (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) :=
    epi_tensor_P_proj ((free ℤ).obj (ℕ∪{∞}).toCondensed)
  apply (cancel_epi (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ)).1
  dsimp [boundedDifferenceMap]
  calc
    (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) ≫
        ((P_proj ℤ ▷ P ℤ) ≫ ((P ℤ ◁ basisMap) ≫
          pTensorDesc boundedIntSequences (P ℤ) boundedDifferenceNumerator boundedDifferenceNumerator_kills))
        = ((((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ basisMapNumerator) ≫
            (P_proj ℤ ▷ boundedIntSequences)) ≫
              pTensorDesc boundedIntSequences (P ℤ) boundedDifferenceNumerator boundedDifferenceNumerator_kills := by
          rw [← freeFreeBasisMap_square]
          simp [Category.assoc]
    _ = (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ basisMapNumerator) ≫
            boundedDifferenceNumerator := by
          rw [Category.assoc]
          rw [pTensorDesc_comp_proj]
    _ = (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ basisMapNumerator) ≫
            boundedDifferenceFreeNumerator ≫ P_proj ℤ := by
          rw [boundedDifferenceFreeNumerator_comp_P_proj]
    _ = (oneMinusShift' ℤ ▷ ((free ℤ).obj (ℕ∪{∞}).toCondensed)) ≫
            pTailFreeFreeLift ≫ P_proj ℤ := by
          simpa [Category.assoc] using
            congrArg (fun q => q ≫ P_proj ℤ) boundedDifferenceFreeNumerator_basisMapNumerator
    _ = (((free ℤ).obj (ℕ∪{∞}).toCondensed) ◁ P_proj ℤ) ≫
        ((P_proj ℤ ▷ P ℤ) ≫ pDifferenceMap) := by
          simpa [Category.assoc] using pDifferenceMap_freeFree_lift.symm

lemma basisMap_boundedTailSection :
    basisMap ≫ boundedTailSection = pTailSection ≫ (P ℤ ◁ basisMap) := by
  dsimp [boundedTailSection, pTailSection]
  rw [leftUnitor_inv_naturality_assoc]
  slice_lhs 2 3 => rw [whisker_exchange]
  simp [Category.assoc]

local instance instIsIso_solidification_map_oneMinusShift_tensor_local (M : LightCondAb) :
    IsIso (solidification.map ((oneMinusShift ℤ) ▷ M)) :=
  solidification_map_oneMinusShift_tensor_isIso M

lemma solidification_whiskerRight_basisMap_inv_comm :
    solidification.map (P ℤ ◁ basisMap) ≫
        inv (solidification.map ((oneMinusShift ℤ) ▷ boundedIntSequences)) =
      inv (solidification.map ((oneMinusShift ℤ) ▷ P ℤ)) ≫
        solidification.map (P ℤ ◁ basisMap) := by
  let σP : P ℤ ⊗ P ℤ ⟶ P ℤ ⊗ P ℤ := (oneMinusShift ℤ) ▷ P ℤ
  let σB : P ℤ ⊗ boundedIntSequences ⟶ P ℤ ⊗ boundedIntSequences :=
    (oneMinusShift ℤ) ▷ boundedIntSequences
  let w : P ℤ ⊗ P ℤ ⟶ P ℤ ⊗ boundedIntSequences := P ℤ ◁ basisMap
  have hcomm : σP ≫ w = w ≫ σB := by
    dsimp [σP, σB, w]
    rw [whisker_exchange]
  have hL : solidification.map σP ≫ solidification.map w =
      solidification.map w ≫ solidification.map σB := by
    simpa [Functor.map_comp] using congrArg (fun f => solidification.map f) hcomm
  haveI : IsIso (solidification.map σP) := solidification_map_oneMinusShift_tensor_isIso (P ℤ)
  haveI : IsIso (solidification.map σB) :=
    solidification_map_oneMinusShift_tensor_isIso boundedIntSequences
  change solidification.map w ≫ inv (solidification.map σB) =
      inv (solidification.map σP) ≫ solidification.map w
  calc
    solidification.map w ≫ inv (solidification.map σB)
        = inv (solidification.map σP) ≫
            (solidification.map σP ≫ solidification.map w) ≫
              inv (solidification.map σB) := by simp [Category.assoc]
    _ = inv (solidification.map σP) ≫
            (solidification.map w ≫ solidification.map σB) ≫
              inv (solidification.map σB) := by rw [hL]
    _ = inv (solidification.map σP) ≫ solidification.map w := by simp [Category.assoc]

/-- Formal SPG9 idempotent reduction assuming the remaining direct P-difference compatibility. -/
lemma boundedShiftRetract_idempotent_eq_identity_of_pDifferenceMap_compat
    (hcompat : (P ℤ ◁ basisMap) ≫ boundedDifferenceMap = pDifferenceMap) :
    solidification.map basisMap ≫ (boundedShiftRetractData.retract).i =
      𝟙 (solidification.obj (P ℤ)) := by
  change solidification.map basisMap ≫
      (solidification.map boundedTailSection ≫
        inv (solidification.map ((oneMinusShift ℤ) ▷ boundedIntSequences)) ≫
          solidification.map boundedDifferenceMap) = 𝟙 (solidification.obj (P ℤ))
  calc
    solidification.map basisMap ≫
        (solidification.map boundedTailSection ≫
          inv (solidification.map ((oneMinusShift ℤ) ▷ boundedIntSequences)) ≫
            solidification.map boundedDifferenceMap)
        = solidification.map pTailSection ≫ solidification.map (P ℤ ◁ basisMap) ≫
          inv (solidification.map ((oneMinusShift ℤ) ▷ boundedIntSequences)) ≫
            solidification.map boundedDifferenceMap := by
          rw [← Category.assoc]
          rw [← Functor.map_comp]
          rw [basisMap_boundedTailSection]
          simp [Functor.map_comp, Category.assoc]
    _ = solidification.map pTailSection ≫
          inv (solidification.map ((oneMinusShift ℤ) ▷ P ℤ)) ≫
            solidification.map (P ℤ ◁ basisMap) ≫
              solidification.map boundedDifferenceMap := by
          slice_lhs 2 3 => rw [solidification_whiskerRight_basisMap_inv_comm]
          simp [Category.assoc]
    _ = solidification.map pTailSection ≫
          inv (solidification.map ((oneMinusShift ℤ) ▷ P ℤ)) ≫
            solidification.map pDifferenceMap := by
          rw [← Functor.map_comp]
          rw [hcompat]
    _ = 𝟙 (solidification.obj (P ℤ)) := by
          dsimp [pDifferenceMap]
          rw [Functor.map_comp]
          calc
            solidification.map pTailSection ≫
                inv (solidification.map ((oneMinusShift ℤ) ▷ P ℤ)) ≫
                  (solidification.map ((oneMinusShift ℤ) ▷ P ℤ) ≫ solidification.map pTailMap)
                = solidification.map pTailSection ≫ solidification.map pTailMap := by simp
            _ = solidification.map (pTailSection ≫ pTailMap) := by rw [Functor.map_comp]
            _ = 𝟙 (solidification.obj (P ℤ)) := by simp [pTailSection_fac]

lemma boundedShiftRetract_idempotent_eq_identity :
    solidification.map basisMap ≫ (boundedShiftRetractData.retract).i =
      𝟙 (solidification.obj (P ℤ)) :=
  boundedShiftRetract_idempotent_eq_identity_of_pDifferenceMap_compat pDifferenceMap_compat

instance instIsIso_solidification_map_basisMap :
    IsIso (solidification.map basisMap) :=
  boundedShiftRetractData.isIso_map_g boundedShiftRetract_idempotent_eq_identity

/-- The solidification of `P ℤ` is the solidification of bounded integer sequences. -/
noncomputable def solidPIsoBounded :
    solidP ≅ solidification.obj boundedIntSequences :=
  asIso (solidification.map basisMap)

@[simp]
lemma solidPIsoBounded_hom :
    solidPIsoBounded.hom = solidification.map basisMap := rfl

/-- Formal SPG9 reduction: once `solidification.map basisMap` is known to be mono, the split-epi
retract from the bounded shift diagram is automatically the two-sided inverse. -/
lemma boundedShiftRetract_idempotent_eq_identity_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    solidification.map basisMap ≫ (boundedShiftRetractData.retract).i =
      𝟙 (solidification.obj (P ℤ)) := by
  apply (cancel_mono (solidification.map basisMap)).1
  calc
    (solidification.map basisMap ≫ (boundedShiftRetractData.retract).i) ≫
        solidification.map basisMap
        = solidification.map basisMap ≫
            ((boundedShiftRetractData.retract).i ≫ solidification.map basisMap) := by
          rw [Category.assoc]
    _ = solidification.map basisMap ≫ 𝟙 (solidification.obj boundedIntSequences) := by
          change solidification.map basisMap ≫
            ((boundedShiftRetractData.retract).i ≫ (boundedShiftRetractData.retract).r) =
              solidification.map basisMap ≫ 𝟙 (solidification.obj boundedIntSequences)
          exact congrArg (fun q => solidification.map basisMap ≫ q)
            boundedShiftRetractData.retract.retract
    _ = 𝟙 (solidification.obj (P ℤ)) ≫ solidification.map basisMap := by
          simp

/-- Conditional isomorphism statement for SPG9.  The remaining mathematical input is the mono
property of `solidification.map basisMap`. -/
lemma isIso_solidification_map_basisMap_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    IsIso (solidification.map basisMap) :=
  boundedShiftRetractData.isIso_map_g
    boundedShiftRetract_idempotent_eq_identity_of_solidified_basisMap_mono

/-- Conditional bounded-sequence identification; this becomes the SPG9 isomorphism once the mono
property of `solidification.map basisMap` is supplied. -/
noncomputable def solidPIsoBounded_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    solidP ≅ solidification.obj boundedIntSequences := by
  letI := isIso_solidification_map_basisMap_of_solidified_basisMap_mono
  exact asIso (solidification.map basisMap)

end ProjectiveGeneratorProof
end Solid
end LightCondensed
