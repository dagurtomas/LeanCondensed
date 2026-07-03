module

public import LeanCondensed.Projects.SolidProjectiveGenerator.NinfSections
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

lemma boundedTailFamilyLinear_naturality {S T : LightProfinite}
    (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
    (m : boundedIntSequences.obj.obj ⟨S⟩) :
    boundedIntSequences.obj.map g.op (boundedTailFamilyLinear S f m) =
      boundedTailFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  apply BoundedIntSeqSection.ext_apply
  intro k t
  change (boundedIntSeqSectionComap g
      (boundedTailFamilySection f (show BoundedIntSeqSection S from m))).val k t =
    (boundedTailFamilySection (g ≫ f)
      (boundedIntSeqSectionComap g (show BoundedIntSeqSection S from m))).val k t
  rfl

lemma boundedTailFamilyLinear_naturality' :
    ∀ {S T : LightProfinite} (g : T ⟶ S) (f : S ⟶ (ℕ∪{∞} : LightProfinite))
      (m : boundedIntSequences.obj.obj ⟨S⟩),
      boundedIntSequences.obj.map g.op (boundedTailFamilyLinear S f m) =
        boundedTailFamilyLinear T (g ≫ f) (boundedIntSequences.obj.map g.op m) := by
  intro S T g f m
  exact boundedTailFamilyLinear_naturality g f m

noncomputable def boundedTailNumerator :
    ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ boundedIntSequences ⟶ boundedIntSequences :=
  freeTensorDescLin (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
    boundedTailFamilyLinear boundedTailFamilyLinear_naturality'



/-- The `n`th finite-point generator in the free object on `ℕ∪∞`. -/
noncomputable def freeNatBasis (n : ℕ) :
    𝟙_ LightCondAb ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  freePointIsoUnit.inv ≫
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n))

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeNatBasis_comp_shift (n : ℕ) :
    freeNatBasis n ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
      freeNatBasis (n + 1) := by
  dsimp [freeNatBasis]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint (n + 1)))
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [natPoint_comp_shift]

set_option backward.isDefEq.respectTransparency false in
lemma freeNatBasis_oneMinusShift' (n : ℕ) :
    freeNatBasis n ≫ oneMinusShift' ℤ = freeNatBasis n - freeNatBasis (n + 1) := by
  dsimp [oneMinusShift']
  change freeNatBasis n ≫
      (𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj (ℕ∪{∞})) -
        (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift) =
    freeNatBasis n - freeNatBasis (n + 1)
  rw [Preadditive.comp_sub]
  rw [freeNatBasis_comp_shift]
  change freeNatBasis n - freeNatBasis (n + 1) = freeNatBasis n - freeNatBasis (n + 1)
  rfl

/-- The `∞` generator in the free object on `ℕ∪∞`. -/
noncomputable def freeInftyBasis :
    𝟙_ LightCondAb ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  freePointIsoUnit.inv ≫ P_map ℤ

@[simp]
lemma iota_comp_shift : ι ≫ LightProfinite.shift = ι := by
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeInftyBasis_comp_shift :
    freeInftyBasis ≫ (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift =
      freeInftyBasis := by
  dsimp [freeInftyBasis, P_map]
  rw [Category.assoc]
  congr 1
  change (free ℤ).map (lightProfiniteToLightCondSet.map ι) ≫
      (free ℤ).map (lightProfiniteToLightCondSet.map LightProfinite.shift) =
    (free ℤ).map (lightProfiniteToLightCondSet.map ι)
  rw [← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [iota_comp_shift]

set_option backward.isDefEq.respectTransparency false in
lemma freeInftyBasis_oneMinusShift' :
    freeInftyBasis ≫ oneMinusShift' ℤ = 0 := by
  dsimp [oneMinusShift']
  change freeInftyBasis ≫
      (𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj (ℕ∪{∞})) -
        (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift) = 0
  rw [Preadditive.comp_sub]
  rw [freeInftyBasis_comp_shift]
  change freeInftyBasis - freeInftyBasis = 0
  abel

/-- The class in `P ℤ` represented by the `n`th finite point of `ℕ∪∞`. -/
noncomputable def pBasis (n : ℕ) : 𝟙_ LightCondAb ⟶ P ℤ :=
  freeNatBasis n ≫ P_proj ℤ

/-- The zeroth-coordinate section used for the tail map in Lemma 3.3.2. -/
noncomputable def tailSection (T : LightProfinite) :
    (free ℤ).obj T.toCondensed ⟶ P ℤ ⊗ (free ℤ).obj T.toCondensed :=
  (λ_ ((free ℤ).obj T.toCondensed)).inv ≫ pBasis 0 ▷ (free ℤ).obj T.toCondensed

/-- The `n`th finite slice of a numerator map `ℤ[ℕ∪∞] ⊗ M ⟶ N`. -/
noncomputable def numeratorSlice (M N : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) : M ⟶ N :=
  (λ_ M).inv ≫ freeNatBasis n ▷ M ≫ f

@[reassoc]
lemma numeratorSlice_comp (M N K : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) (g : N ⟶ K) :
    numeratorSlice M K n (f ≫ g) = numeratorSlice M N n f ≫ g := by
  dsimp [numeratorSlice]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Slicing after precomposition by `1 - shift` takes finite differences of slices. -/
lemma numeratorSlice_oneMinusShift' (M N : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    numeratorSlice M N n ((oneMinusShift' ℤ ▷ M) ≫ f) =
      numeratorSlice M N n f - numeratorSlice M N (n + 1) f := by
  dsimp [numeratorSlice]
  rw [← comp_whiskerRight_assoc]
  rw [freeNatBasis_oneMinusShift']
  rw [IntProof.sub_whiskerRight]
  rw [Preadditive.sub_comp]
  rw [Preadditive.comp_sub]

/-- The `n`th finite value of a map out of the free object on `ℕ∪∞`. -/
noncomputable def freeNatValue (N : LightCondAb) (n : ℕ)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N) :
    (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ N :=
  (free ℤ).map (lightProfiniteToLightCondSet.map (natPoint n)) ≫ f

/-- The `n`th finite value of a map built from a section over `ℕ∪∞` is obtained by restricting
that section to the point `n`. -/
lemma freeNatValue_of_freeElement (A : LightCondAb) (n : ℕ)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩) :
    freeNatValue A n ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) =
      (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm
        (A.obj.map (natPoint n).op x) := by
  dsimp [freeNatValue]
  rw [freeHomEquivPoints_symm_map]

/-- The `∞` value of a map out of the free object on `ℕ∪∞`. -/
noncomputable def freeInftyValue (N : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N) : 𝟙_ LightCondAb ⟶ N :=
  freeInftyBasis ≫ f

/-- The `∞` value of a map built from a section over `ℕ∪∞` is obtained by restricting that
section to the point `∞`. -/
lemma freeInftyValue_of_freeElement (A : LightCondAb)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩) :
    freeInftyValue A ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) =
      freePointIsoUnit.inv ≫
        (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm (A.obj.map ι.op x) := by
  dsimp [freeInftyValue, freeInftyBasis, P_map]
  rw [Category.assoc]
  rw [freeHomEquivPoints_symm_map]

/-- A section over `ℕ∪∞` whose restriction to `∞` is zero gives a free numerator with zero
`∞` value. -/
lemma freeInftyValue_zero_of_element_infty (A : LightCondAb)
    (x : A.obj.obj ⟨(ℕ∪{∞} : LightProfinite)⟩)
    (h : (freeHomEquivPoints (LightProfinite.of PUnit.{1}) A).symm (A.obj.map ι.op x) = 0) :
    freeInftyValue A ((freeHomEquivPoints (ℕ∪{∞}) A).symm x) = 0 := by
  rw [freeInftyValue_of_freeElement]
  rw [h]
  simp

/-- If a map out of `ℤ[ℕ∪∞]` is zero at `∞`, then it kills the denominator defining `P ℤ`. -/
lemma freeNumerator_kills_of_inftyValue_zero (N : LightCondAb)
    (f : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ N)
    (h : freeInftyValue N f = 0) :
    P_map ℤ ≫ f = 0 := by
  haveI : IsIso freePointIsoUnit.inv := by infer_instance
  apply (cancel_epi freePointIsoUnit.inv).1
  dsimp [freeInftyValue, freeInftyBasis] at h ⊢
  simpa [Category.assoc] using h

/-- The `i`th coordinate of the standard basis family on `ℕ∪∞`. -/
def boundedStandardBasisCoord (i : ℕ) : LocallyConstant (ℕ∪{∞} : LightProfinite) ℤ where
  toFun x :=
    match x with
    | ∞ => 0
    | OnePoint.some n => if n = i then 1 else 0
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_continuous _).mpr
    apply continuous_ninf_of_eventually_eq_zero
    exact Filter.eventually_atTop.2 ⟨i + 1, by
      intro n hn
      simp [Nat.ne_of_gt hn]⟩

@[simp]
lemma boundedStandardBasisCoord_finite (i n : ℕ) :
    boundedStandardBasisCoord i (n : ℕ∪{∞}) = if n = i then 1 else 0 :=
  rfl

@[simp]
lemma boundedStandardBasisCoord_infty (i : ℕ) :
    boundedStandardBasisCoord i (∞ : ℕ∪{∞}) = 0 :=
  rfl

/-- The standard-basis section of the bounded-sequence sheaf over `ℕ∪∞`. -/
def boundedStandardBasisSection : BoundedIntSeqSection (ℕ∪{∞} : LightProfinite) where
  val i := boundedStandardBasisCoord i
  isBounded := by
    refine ⟨1, ?_⟩
    intro x i
    cases x using OnePoint.rec with
    | infty => norm_num [boundedStandardBasisCoord]
    | coe n => by_cases h : n = i <;> norm_num [boundedStandardBasisCoord, h]

/-- The numerator for the standard-basis map `P ℤ ⟶ boundedIntSequences`. -/
noncomputable def basisMapNumerator :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ boundedIntSequences :=
  (freeHomEquivPoints (ℕ∪{∞}) boundedIntSequences).symm
    ((boundedIntSequencesSectionsEquiv (ℕ∪{∞} : LightProfinite)).symm
      boundedStandardBasisSection)

lemma basisMapNumerator_infty :
    freeInftyValue boundedIntSequences basisMapNumerator = 0 := by
  apply freeInftyValue_zero_of_element_infty
  apply (freeHomEquivPoints (LightProfinite.of PUnit.{1}) boundedIntSequences).injective
  rw [Equiv.apply_symm_apply, freeHomEquivPoints_zero]
  apply BoundedIntSeqSection.ext_apply
  intro n s
  cases s
  rfl

lemma basisMapNumerator_kills : P_map ℤ ≫ basisMapNumerator = 0 :=
  freeNumerator_kills_of_inftyValue_zero boundedIntSequences basisMapNumerator
    basisMapNumerator_infty

/-- The map from `P ℤ` sending the finite generator `n` to the standard basis vector `e_n` and
`∞` to zero. -/
noncomputable def basisMap : P ℤ ⟶ boundedIntSequences :=
  P_homMk ℤ boundedIntSequences basisMapNumerator basisMapNumerator_kills

@[reassoc]
lemma P_proj_comp_basisMap : P_proj ℤ ≫ basisMap = basisMapNumerator := by
  change cokernel.π (P_map ℤ) ≫
      cokernel.desc (P_map ℤ) basisMapNumerator basisMapNumerator_kills = basisMapNumerator
  exact cokernel.π_desc (P_map ℤ) basisMapNumerator basisMapNumerator_kills

@[simp]
lemma basisMap_apply_finite_coord (n i : ℕ) :
    (boundedIntSequencesSectionsEquiv (LightProfinite.of PUnit.{1})
      (freeHomEquivPoints (LightProfinite.of PUnit.{1}) boundedIntSequences
        (freeNatValue boundedIntSequences n (P_proj ℤ ≫ basisMap)))).val i PUnit.unit =
      if n = i then 1 else 0 := by
  rw [P_proj_comp_basisMap]
  dsimp [basisMapNumerator]
  rw [freeNatValue_of_freeElement]
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
lemma basisMap_apply_infty (i : ℕ) :
    (boundedIntSequencesSectionsEquiv (LightProfinite.of PUnit.{1})
      (boundedIntSequences.obj.map ι.op
        (freeHomEquivPoints (ℕ∪{∞}) boundedIntSequences (P_proj ℤ ≫ basisMap)))).val i
        PUnit.unit = 0 := by
  rw [P_proj_comp_basisMap]
  dsimp [basisMapNumerator]
  rw [Equiv.apply_symm_apply]
  rfl

/-- The `i`th coordinate map from bounded sequences to `Zdisc`. -/
noncomputable def boundedCoord (i : ℕ) : boundedIntSequences ⟶ Zdisc :=
  boundedToProduct ≫ productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) i

@[simp]
lemma boundedCoord_apply (S : LightProfinite) (x : boundedIntSequences.obj.obj ⟨S⟩)
    (i : ℕ) :
    zdiscSectionsEquiv S ((boundedCoord i).hom.app ⟨S⟩ x) =
      (boundedIntSequencesSectionsEquiv S x).val i := by
  dsimp [boundedCoord]
  change zdiscSectionsEquiv S
      (((productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) i).hom.app ⟨S⟩)
        ((boundedToProduct.hom.app ⟨S⟩) x)) =
    (boundedIntSequencesSectionsEquiv S x).val i
  rw [← productIntSectionsEquiv_apply]
  rw [← productIntLocallyConstantSectionsEquiv_apply]
  rw [boundedToProduct_apply_coord]

lemma P_proj_comp_basisMap_boundedCoord (i : ℕ) :
    P_proj ℤ ≫ basisMap ≫ boundedCoord i =
      zdiscMapOfLocallyConstant (ℕ∪{∞} : LightProfinite) (boundedStandardBasisCoord i) := by
  rw [← Category.assoc]
  rw [P_proj_comp_basisMap]
  apply (freeHomEquivPoints (ℕ∪{∞}) Zdisc).injective
  apply (zdiscSectionsEquiv (ℕ∪{∞} : LightProfinite)).injective
  rw [freeHomEquivPoints_comp]
  dsimp [basisMapNumerator]
  rw [Equiv.apply_symm_apply]
  rw [boundedCoord_apply]
  rw [freeHomEquivPoints_zdiscMapOfLocallyConstant]
  rw [LinearEquiv.apply_symm_apply]
  rw [Equiv.apply_symm_apply]
  rfl

/-- The `∞` slice of a numerator map `ℤ[ℕ∪∞] ⊗ M ⟶ N`. -/
noncomputable def inftySlice (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) : M ⟶ N :=
  (λ_ M).inv ≫ freeInftyBasis ▷ M ≫ f

@[reassoc]
lemma inftySlice_comp (M N K : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) (g : N ⟶ K) :
    inftySlice M K (f ≫ g) = inftySlice M N f ≫ g := by
  dsimp [inftySlice]
  simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The `∞` slice after precomposition by `1 - shift` is zero. -/
lemma inftySlice_oneMinusShift' (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N) :
    inftySlice M N ((oneMinusShift' ℤ ▷ M) ≫ f) = 0 := by
  dsimp [inftySlice]
  rw [← comp_whiskerRight_assoc]
  rw [freeInftyBasis_oneMinusShift']
  simp

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Numerator maps to bounded sequences are determined by their finite slices and their `∞`
slice. -/
lemma boundedTarget_numerator_ext_of_slices
    (g₁ g₂ : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ boundedIntSequences ⟶
      boundedIntSequences)
    (hfinite : ∀ n : ℕ,
      numeratorSlice boundedIntSequences boundedIntSequences n g₁ =
        numeratorSlice boundedIntSequences boundedIntSequences n g₂)
    (hinfty : inftySlice boundedIntSequences boundedIntSequences g₁ =
      inftySlice boundedIntSequences boundedIntSequences g₂) :
    g₁ = g₂ := by
  apply freeTensorHom_ext (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
  intro S f r m
  conv_lhs => rw [freeTensorHomEval_zsmul]
  conv_rhs => rw [freeTensorHomEval_zsmul]
  congr 1
  apply BoundedIntSeqSection.ext_apply
  intro k s
  let pt : LightProfinite := LightProfinite.of PUnit.{1}
  let ps : pt ⟶ S := pointMap S s
  let mpt : boundedIntSequences.obj.obj ⟨pt⟩ := boundedIntSequences.obj.map ps.op m
  have hpt :
      freeTensorHomEval (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
          g₁ pt (ps ≫ f) 1 mpt =
        freeTensorHomEval (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
          g₂ pt (ps ≫ f) 1 mpt := by
    cases hfs : f s using OnePoint.rec with
    | infty =>
        have hpoint : ps ≫ f = ι := by
          ext u
          change f s = (∞ : ℕ∪{∞})
          exact hfs
        subst mpt
        rw [hpoint]
        have hto : toPointMap pt ≫ ι = ι := by ext u; rfl
        rw [← hto]
        have hs := congrArg (fun q => q.hom.app ⟨pt⟩ (boundedIntSequences.obj.map ps.op m)) hinfty
        rw [freeTensorHomEval_point_one, freeTensorHomEval_point_one]
        simpa [inftySlice, freeInftyBasis, P_map, pt] using hs
    | coe n =>
        have hpoint : ps ≫ f = natPoint n := by
          ext u
          change f s = (n : ℕ∪{∞})
          exact hfs
        subst mpt
        rw [hpoint]
        have hto : toPointMap pt ≫ natPoint n = natPoint n := by ext u; rfl
        rw [← hto]
        have hs := congrArg (fun q => q.hom.app ⟨pt⟩ (boundedIntSequences.obj.map ps.op m))
          (hfinite n)
        rw [freeTensorHomEval_point_one, freeTensorHomEval_point_one]
        simpa [numeratorSlice, freeNatBasis, pt] using hs
  have hnat₁ := freeTensorHomEval_naturality_one (ℕ∪{∞} : LightProfinite)
    boundedIntSequences boundedIntSequences g₁ ps f m
  have hnat₂ := freeTensorHomEval_naturality_one (ℕ∪{∞} : LightProfinite)
    boundedIntSequences boundedIntSequences g₂ ps f m
  have hmap : boundedIntSequences.obj.map ps.op
        (freeTensorHomEval (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
          g₁ S f 1 m) =
      boundedIntSequences.obj.map ps.op
        (freeTensorHomEval (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
          g₂ S f 1 m) := by
    rw [hnat₁, hnat₂]
    exact hpt
  have hcoord := congrArg (fun y : boundedIntSequences.obj.obj ⟨pt⟩ =>
      (boundedIntSequencesSectionsEquiv pt y).val k PUnit.unit) hmap
  change (boundedIntSeqSectionComap ps
      (show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₁ S f 1 m)).val k
        PUnit.unit =
    (boundedIntSeqSectionComap ps
      (show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₂ S f 1 m)).val k
        PUnit.unit at hcoord
  change ((show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₁ S f 1 m).val k)
        (ps PUnit.unit) =
    ((show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₂ S f 1 m).val k)
        (ps PUnit.unit) at hcoord
  have hps_apply : ps PUnit.unit = s := rfl
  rw [hps_apply] at hcoord
  change ((show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₁ S f 1 m).val k) s =
    ((show BoundedIntSeqSection S from freeTensorHomEval
        (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences g₂ S f 1 m).val k) s
  exact hcoord

/-- If the `∞` slice of a numerator is zero, then it kills the denominator defining `P ℤ`. -/
lemma numerator_kills_of_inftySlice_zero (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (h : inftySlice M N f = 0) :
    (P_map ℤ ▷ M) ≫ f = 0 := by
  let u : M ⟶ (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⊗ M :=
    (λ_ M).inv ≫ freePointIsoUnit.inv ▷ M
  haveI : IsIso u := by dsimp [u]; infer_instance
  apply (cancel_epi u).1
  calc
    u ≫ ((P_map ℤ ▷ M) ≫ f)
        = inftySlice M N f := by
          dsimp [u, inftySlice, freeInftyBasis]
          simp only [Category.assoc]
          rw [comp_whiskerRight]
          simp [Category.assoc]
    _ = u ≫ (0 : (free ℤ).obj (LightProfinite.of PUnit.{1}).toCondensed ⊗ M ⟶ N) := by
          rw [h]
          simp

/-- Descend a map out of `ℤ[ℕ∪∞] ⊗ M` which kills the basepoint summand to a map out of
`P ℤ ⊗ M`. -/
noncomputable def pTensorDesc (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) :
    P ℤ ⊗ M ⟶ N := by
  refine (PreservesCoequalizer.iso (tensorRight M) (P_map ℤ) 0).inv ≫ coequalizer.desc f ?_
  rw [Functor.map_zero, zero_comp]
  exact hf

set_option backward.isDefEq.respectTransparency false in
lemma epi_P_proj_tensor (M : LightCondAb) : Epi (P_proj ℤ ▷ M) := by
  change Epi ((tensorRight M).map (coequalizer.π (P_map ℤ) 0))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pTensorDesc_comp_proj (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) :
    (P_proj ℤ ▷ M) ≫ pTensorDesc M N f hf = f := by
  dsimp [pTensorDesc, P_proj]
  simpa using (map_π_preserves_coequalizer_inv_desc (G := tensorRight M)
    (f := P_map ℤ) (g := 0) (k := f) (by rw [Functor.map_zero, zero_comp]; exact hf))

/-- Slicing a descended numerator at a finite basis element recovers the corresponding numerator
slice. -/
lemma pTensorDesc_slice (M N : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ M ⟶ N)
    (hf : (P_map ℤ ▷ M) ≫ f = 0) (n : ℕ) :
    ((λ_ M).inv ≫ pBasis n ▷ M) ≫ pTensorDesc M N f hf =
      numeratorSlice M N n f := by
  dsimp [pBasis, numeratorSlice]
  simp only [Category.assoc]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [pTensorDesc_comp_proj]

/-- The bounded-tail family at the finite point `n` is the `n`th tail projection. -/
lemma boundedTailFamilyMap_natPoint (n : ℕ) :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
      boundedTailFamilyLinear boundedTailFamilyLinear_naturality' (natPoint n) =
    boundedTailProjection n := by
  ext S x
  change boundedTailFamilyLinear S.unop (toPointMap S.unop ≫ natPoint n) x =
    (boundedTailProjection n).hom.app S x
  apply BoundedIntSeqSection.ext_apply
  intro k s
  dsimp [boundedTailFamilyLinear, boundedTailProjection, boundedTailProjectionSection]
  change boundedTailFamilyCoord k ((toPointMap S.unop ≫ natPoint n) s) * x.val k s =
    (if n ≤ k then x.val k else 0) s
  change boundedTailFamilyCoord k (n : ℕ∪{∞}) * x.val k s = _
  rw [boundedTailFamilyCoord_finite]
  by_cases h : n ≤ k <;> simp [h]

/-- Finite slices of the bounded-tail numerator are the tail projections. -/
lemma boundedTailNumerator_slice (n : ℕ) :
    numeratorSlice boundedIntSequences boundedIntSequences n boundedTailNumerator =
      boundedTailProjection n := by
  dsimp [numeratorSlice, freeNatBasis, boundedTailNumerator]
  rw [freeTensorDescLin_point]
  exact boundedTailFamilyMap_natPoint n

/-- The bounded-tail family at `∞` is zero. -/
lemma boundedTailFamilyMap_infty :
    freeTensorFamilyMap (ℕ∪{∞} : LightProfinite) boundedIntSequences boundedIntSequences
      boundedTailFamilyLinear boundedTailFamilyLinear_naturality' ι =
    0 := by
  ext S x
  change boundedTailFamilyLinear S.unop (toPointMap S.unop ≫ ι) x =
    (0 : boundedIntSequences ⟶ boundedIntSequences).hom.app S x
  apply BoundedIntSeqSection.ext_apply
  intro k s
  change boundedTailFamilyCoord k ((toPointMap S.unop ≫ ι) s) * x.val k s = 0
  change boundedTailFamilyCoord k (∞ : ℕ∪{∞}) * x.val k s = 0
  rw [boundedTailFamilyCoord_infty]
  simp

/-- The bounded-tail numerator has zero `∞` slice. -/
lemma boundedTailNumerator_infty :
    inftySlice boundedIntSequences boundedIntSequences boundedTailNumerator = 0 := by
  dsimp [inftySlice, freeInftyBasis, P_map, boundedTailNumerator]
  rw [freeTensorDescLin_point]
  exact boundedTailFamilyMap_infty

/-- The bounded-tail numerator kills the basepoint summand and therefore descends to `P`. -/
lemma boundedTailNumerator_kills :
    (P_map ℤ ▷ boundedIntSequences) ≫ boundedTailNumerator = 0 :=
  numerator_kills_of_inftySlice_zero boundedIntSequences boundedIntSequences
    boundedTailNumerator boundedTailNumerator_infty

/-- The bounded-tail map descended from the bounded-tail numerator. -/
noncomputable def boundedTailMap :
    P ℤ ⊗ boundedIntSequences ⟶ boundedIntSequences :=
  pTensorDesc boundedIntSequences boundedIntSequences boundedTailNumerator
    boundedTailNumerator_kills

/-- Finite slices of the descended bounded-tail map are the tail projections. -/
lemma boundedTailMap_slice (n : ℕ) :
    ((λ_ boundedIntSequences).inv ≫ pBasis n ▷ boundedIntSequences) ≫ boundedTailMap =
      boundedTailProjection n := by
  dsimp [boundedTailMap]
  rw [pTensorDesc_slice]
  exact boundedTailNumerator_slice n

/-- The zeroth bounded-tail section. -/
noncomputable def boundedTailSection :
    boundedIntSequences ⟶ P ℤ ⊗ boundedIntSequences :=
  (λ_ boundedIntSequences).inv ≫ pBasis 0 ▷ boundedIntSequences

/-- The bounded-tail section splits the bounded-tail map. -/
lemma boundedTailSection_fac :
    boundedTailSection ≫ boundedTailMap = 𝟙 boundedIntSequences := by
  rw [boundedTailSection, boundedTailMap_slice]
  exact boundedTailProjection_zero

-- The free tensor isomorphism is natural in the left variable.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_naturality_left {A' A S : LightProfinite} (φ : A' ⟶ A) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map φ) ▷ (free ℤ).obj S.toCondensed) ≫
        (IntProof.freeTensorIsoInt A S).hom =
      (IntProof.freeTensorIsoInt A' S).hom ≫
        (free ℤ).map (lightProfiniteToLightCondSet.map (φ ⊗ₘ 𝟙 S)) := by
  dsimp [IntProof.freeTensorIsoInt]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc (free ℤ)
    (lightProfiniteToLightCondSet.map φ) S.toCondensed
    ((free ℤ).map (Functor.LaxMonoidal.μ lightProfiniteToLightCondSet A S))]
  slice_lhs 2 4 => rw [← Functor.map_comp]
  slice_rhs 2 4 => rw [← Functor.map_comp]
  rw [Functor.LaxMonoidal.μ_natural_left lightProfiniteToLightCondSet]
  simp [MonoidalCategory.tensorHom_id]

-- The free tensor isomorphism is compatible with the left unit after identifying the chosen
-- point-object with the tensor unit.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_leftUnit (T : LightProfinite) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freePointIsoUnit.inv ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (LightProfinite.of PUnit.{1}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (λ_ T).inv) := by
  dsimp [IntProof.freeTensorIsoInt, freePointIsoUnit]
  simp [← Functor.map_comp]
  change (free ℤ).map
      ((λ_ (lightProfiniteToLightCondSet.obj T)).inv ≫
        (Functor.LaxMonoidal.ε lightProfiniteToLightCondSet ▷ lightProfiniteToLightCondSet.obj T) ≫
          Functor.LaxMonoidal.μ lightProfiniteToLightCondSet (𝟙_ LightProfinite) T) =
    (free ℤ).map (lightProfiniteToLightCondSet.map (λ_ T).inv)
  rw [Functor.LaxMonoidal.left_unitality_inv]

-- Compatibility of the free tensor isomorphism with finite slices.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_finiteTensorPoint (T : LightProfinite) (n : ℕ) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freeNatBasis n ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (finiteTensorPoint T n)) := by
  dsimp [freeNatBasis]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [freeTensorIsoInt_hom_naturality_left]
  rw [freeTensorIsoInt_hom_leftUnit_assoc]
  dsimp [finiteTensorPoint]
  rw [← Functor.map_comp]
  congr 1

-- Compatibility of the free tensor isomorphism with the `∞` slice.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma freeTensorIsoInt_hom_inftyTensorPoint (T : LightProfinite) :
    (λ_ ((free ℤ).obj T.toCondensed)).inv ≫
      freeInftyBasis ▷ (free ℤ).obj T.toCondensed ≫
      (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom =
    (free ℤ).map (lightProfiniteToLightCondSet.map (inftyTensorPoint T)) := by
  dsimp [freeInftyBasis, P_map]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [freeTensorIsoInt_hom_naturality_left]
  rw [freeTensorIsoInt_hom_leftUnit_assoc]
  dsimp [inftyTensorPoint]
  rw [← Functor.map_comp]
  congr 1

/-- Finite slices of a numerator built from a section over `(ℕ∪∞) × T` are obtained by
restricting that section along the finite slice map. -/
lemma numeratorSlice_of_freeTensorElement (T : LightProfinite) (A : LightCondAb) (n : ℕ)
    (x : A.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩) :
    numeratorSlice ((free ℤ).obj T.toCondensed) A n
      ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
        (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x) =
      (freeHomEquivPoints T A).symm (A.obj.map (finiteTensorPoint T n).op x) := by
  dsimp [numeratorSlice]
  rw [freeTensorIsoInt_hom_finiteTensorPoint_assoc]
  rw [freeHomEquivPoints_symm_map]

/-- The `∞` slice of a numerator built from a section over `(ℕ∪∞) × T` is obtained by
restricting that section along the `∞` slice map. -/
lemma inftySlice_of_freeTensorElement (T : LightProfinite) (A : LightCondAb)
    (x : A.obj.obj ⟨((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite)⟩) :
    inftySlice ((free ℤ).obj T.toCondensed) A
      ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
        (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x) =
      (freeHomEquivPoints T A).symm (A.obj.map (inftyTensorPoint T).op x) := by
  dsimp [inftySlice]
  rw [freeTensorIsoInt_hom_inftyTensorPoint_assoc]
  rw [freeHomEquivPoints_symm_map]

/-- Finite slices of an arbitrary numerator can be read from the corresponding section over
`(ℕ∪∞) × T`. -/
lemma numeratorSlice_eq_symm_map_finite (T : LightProfinite) (A : LightCondAb) (n : ℕ)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ A) :
    numeratorSlice ((free ℤ).obj T.toCondensed) A n f =
      (freeHomEquivPoints T A).symm
        (A.obj.map (finiteTensorPoint T n).op
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
            ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f))) := by
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  have hf : f = (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
      (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x := by
    dsimp [x]
    simp
  change numeratorSlice ((free ℤ).obj T.toCondensed) A n f =
      (freeHomEquivPoints T A).symm (A.obj.map (finiteTensorPoint T n).op x)
  rw [hf]
  rw [numeratorSlice_of_freeTensorElement]

/-- The `∞` slice of an arbitrary numerator can be read from the corresponding section over
`(ℕ∪∞) × T`. -/
lemma inftySlice_eq_symm_map_infty (T : LightProfinite) (A : LightCondAb)
    (f : ((free ℤ).obj (ℕ∪{∞}).toCondensed) ⊗ (free ℤ).obj T.toCondensed ⟶ A) :
    inftySlice ((free ℤ).obj T.toCondensed) A f =
      (freeHomEquivPoints T A).symm
        (A.obj.map (inftyTensorPoint T).op
          (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
            ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f))) := by
  let x := freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A
    ((IntProof.freeTensorIsoInt (ℕ∪{∞}) T).inv ≫ f)
  have hf : f = (IntProof.freeTensorIsoInt (ℕ∪{∞}) T).hom ≫
      (freeHomEquivPoints ((ℕ∪{∞} : LightProfinite) ⊗ T : LightProfinite) A).symm x := by
    dsimp [x]
    simp
  change inftySlice ((free ℤ).obj T.toCondensed) A f =
      (freeHomEquivPoints T A).symm (A.obj.map (inftyTensorPoint T).op x)
  rw [hf]
  rw [inftySlice_of_freeTensorElement]

end ProjectiveGeneratorProof
end Solid
end LightCondensed
