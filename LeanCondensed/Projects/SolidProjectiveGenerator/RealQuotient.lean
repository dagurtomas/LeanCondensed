module

public import LeanCondensed.Projects.SolidProjectiveGenerator.RealSequences
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import Mathlib.Topology.Separation.DisjointCover

@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators Topology

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- Cast a locally constant integer-valued function to a continuous real-valued function. -/
noncomputable def locallyConstantIntToRealLinear (S : LightProfinite) :
    LocallyConstant S ℤ →ₗ[ℤ] C(S, ℝ) where
  toFun f := ((f.map fun z : ℤ => (z : ℝ)) : LocallyConstant S ℝ)
  map_add' := by
    intro f g
    ext s
    simp [LocallyConstant.map]
  map_smul' := by
    intro a f
    ext s
    change ((a • f s : ℤ) : ℝ) = (a • (f s : ℝ) : ℝ)
    simp

@[simp]
lemma locallyConstantIntToRealLinear_apply (S : LightProfinite)
    (f : LocallyConstant S ℤ) (s : S) :
    locallyConstantIntToRealLinear S f s = (f s : ℝ) :=
  rfl

/-- The continuous `ℤ`-linear cast from the discrete topological integers to the real line. -/
noncomputable def intTopModuleToReal :
    LightCondAb.discreteIntTopModule ⟶ LightCondAb.realTopModule :=
  TopModuleCat.ofHom ({
    toLinearMap := {
      toFun := fun z : ℤ => (z : ℝ)
      map_add' := by intro x y; norm_num
      map_smul' := by
        intro a z
        simp only [zsmul_eq_mul, Int.cast_mul]
        rfl }
    cont := continuous_of_discreteTopology } : ℤ →L[ℤ] ℝ)

/-- Cast the discrete integer sheaf to the represented real-line sheaf. -/
noncomputable def zdiscToReal : Zdisc ⟶ realCondensedAb :=
  LightCondAb.discreteIntTopModuleCondensedIso.inv ≫
    LightCondensed.topModuleToLightCondAbMap intTopModuleToReal

@[simp]
lemma zdiscToReal_apply (S : LightProfinite) (x : Zdisc.obj.obj ⟨S⟩) :
    realCondensedAbSectionsEquiv S ((zdiscToReal.hom.app ⟨S⟩) x) =
      locallyConstantIntToRealLinear S (zdiscSectionsEquiv S x) := by
  dsimp [zdiscToReal, realCondensedAb, LightCondensed.topModuleToLightCondAbMap]
  let y0 := LightCondAb.discreteIntTopModuleCondensedIso.inv.hom.app ⟨S⟩ x
  have hx : LightCondAb.discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩ y0 = x := by
    dsimp [y0]
    change (LightCondAb.discreteIntTopModuleCondensedIso.inv ≫
      LightCondAb.discreteIntTopModuleCondensedIso.hom).hom.app ⟨S⟩ x = x
    rw [Iso.inv_hom_id]
    rfl
  have hy : zdiscSectionsEquiv S x = LightCondAb.discreteIntTopModuleSectionsEquiv S y0 := by
    have h := LightCondAb.discreteIntTopModuleCondensedIso_sections S y0
    rw [← hx]
    change ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      (LightCondAb.discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩ y0) =
        LightCondAb.discreteIntTopModuleSectionsEquiv S y0
    exact h
  ext s
  change (intTopModuleToReal.hom ((show C(S, ℤ) from y0) s) : ℝ) =
    (locallyConstantIntToRealLinear S (zdiscSectionsEquiv S x)) s
  rw [locallyConstantIntToRealLinear_apply, hy]
  rfl

/-- Coordinatewise cast from integer sequences to real sequences. -/
noncomputable def productIntToProductReal : productIntLight ⟶ productRealSequences :=
  Pi.lift fun n : ℕ =>
    productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n ≫ zdiscToReal

@[simp]
lemma productIntToProductReal_π (n : ℕ) :
    productIntToProductReal ≫ Pi.π (fun _ : ℕ => realCondensedAb) n =
      productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n ≫ zdiscToReal := by
  exact Pi.lift_π (fun n : ℕ =>
    productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n ≫ zdiscToReal) n

@[simp]
lemma productIntToProductReal_apply_coord (S : LightProfinite)
    (x : productIntLight.obj.obj ⟨S⟩) (n : ℕ) :
    productRealSequencesSectionsEquiv S ((productIntToProductReal.hom.app ⟨S⟩) x) n =
      locallyConstantIntToRealLinear S (productIntLocallyConstantSectionsEquiv S x n) := by
  rw [productRealSequencesSectionsEquiv_apply]
  change realCondensedAbSectionsEquiv S
      (((productIntToProductReal ≫ Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩) x) =
    locallyConstantIntToRealLinear S (productIntLocallyConstantSectionsEquiv S x n)
  rw [productIntToProductReal_π n]
  change realCondensedAbSectionsEquiv S
      ((zdiscToReal.hom.app ⟨S⟩)
        (((productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩) x)) =
    locallyConstantIntToRealLinear S (productIntLocallyConstantSectionsEquiv S x n)
  rw [zdiscToReal_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Coordinatewise cast from bounded integer sequences to bounded real sequences. -/
noncomputable def boundedIntToBoundedReal : boundedIntSequences ⟶ boundedRealSequences where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => (show BoundedRealSeqSection S.unop from {
        val := fun n => locallyConstantIntToRealLinear S.unop
          ((boundedIntSequencesSectionsEquiv S.unop x).val n)
        isBounded := by
          obtain ⟨N, hN⟩ := (boundedIntSequencesSectionsEquiv S.unop x).isBounded
          refine ⟨N, ?_⟩
          intro s n
          rw [locallyConstantIntToRealLinear_apply]
          rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs]
          exact_mod_cast hN s n })
      map_add' := by
        intro x y
        apply BoundedRealSeqSection.ext_apply
        intro n s
        change ((((x + y : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)) =
          (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ) +
            (((y : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)
        rw [BoundedIntSeqSection.val_add]
        change ((((x : BoundedIntSeqSection S.unop).val n s +
          (y : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)) =
          (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ) +
            (((y : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)
        rw [Int.cast_add]
      map_smul' := by
        intro a x
        apply BoundedRealSeqSection.ext_apply
        intro n s
        change ((((a • x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)) =
          (a • (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ) : ℝ)
        rw [BoundedIntSeqSection.val_zsmul]
        change (((a * ((x : BoundedIntSeqSection S.unop).val n s) : ℤ) : ℝ)) =
          (a • (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ) : ℝ)
        rw [Int.cast_mul]
        change ((a : ℝ) * (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ)) =
          (a • (((x : BoundedIntSeqSection S.unop).val n s : ℤ) : ℝ) : ℝ)
        rw [zsmul_eq_mul] }
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext x
      apply BoundedRealSeqSection.ext_apply
      intro n s
      rfl }

@[simp]
lemma boundedIntToBoundedReal_apply_coord (S : LightProfinite)
    (x : boundedIntSequences.obj.obj ⟨S⟩) (n : ℕ) :
    (boundedRealSequencesSectionsEquiv S ((boundedIntToBoundedReal.hom.app ⟨S⟩) x)).1 n =
      locallyConstantIntToRealLinear S ((boundedIntSequencesSectionsEquiv S x).val n) := by
  dsimp [boundedIntToBoundedReal, boundedRealSequencesSectionsEquiv,
    BoundedRealSeqSection.subtypeLinearEquiv]
  rfl

/-- Every continuous real-valued function on a light profinite space is within distance `2` of a
locally constant integer-valued function. -/
lemma exists_locallyConstant_int_approx (S : LightProfinite) (f : C(S, ℝ)) :
    ∃ g : LocallyConstant S ℤ, ∀ s : S, ‖f s - (g s : ℝ)‖ ≤ (2 : ℝ) := by
  let R : Set (ℝ × ℝ) := {p | |p.1 - p.2| < (1 : ℝ)}
  have hRopen : IsOpen R := by
    dsimp [R]
    exact isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ => |p.1 - p.2|) continuous_const
  have hRdiag : R ∈ nhdsSet (Set.diagonal ℝ) := by
    rw [mem_nhdsSet_iff_forall]
    intro p hp
    rcases p with ⟨x, y⟩
    simp only [Set.mem_diagonal_iff] at hp
    subst y
    exact IsOpen.mem_nhds hRopen (by simp [R])
  obtain ⟨n, idx, hval, hidx_cont, happrox⟩ :=
    ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal f hRdiag
  let idxLC : LocallyConstant S (Fin n) :=
    ⟨idx, (IsLocallyConstant.iff_continuous idx).2 hidx_cont⟩
  let z : Fin n → ℤ := fun i => ⌊hval i⌋
  let g : LocallyConstant S ℤ := idxLC.map z
  refine ⟨g, ?_⟩
  intro s
  have hdist : |f s - hval (idx s)| < (1 : ℝ) := happrox s
  have hfloor_le : (⌊hval (idx s)⌋ : ℝ) ≤ hval (idx s) := Int.floor_le _
  have hlt : hval (idx s) < (⌊hval (idx s)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have habs_floor : |hval (idx s) - (⌊hval (idx s)⌋ : ℝ)| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hfloor_le)]
    linarith
  change ‖f s - (⌊hval (idx s)⌋ : ℝ)‖ ≤ (2 : ℝ)
  rw [Real.norm_eq_abs]
  calc
    |f s - (⌊hval (idx s)⌋ : ℝ)| =
        |(f s - hval (idx s)) + (hval (idx s) - (⌊hval (idx s)⌋ : ℝ))| := by ring_nf
    _ ≤ |f s - hval (idx s)| + |hval (idx s) - (⌊hval (idx s)⌋ : ℝ)| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add hdist.le habs_floor
    _ = (2 : ℝ) := by norm_num

/-- A chosen coordinatewise locally constant integer approximation to a real sequence. -/
noncomputable def productRealIntApprox (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) : productIntLight.obj.obj ⟨S⟩ :=
  (productIntLocallyConstantSectionsEquiv S).symm
    (fun n => (exists_locallyConstant_int_approx S (productRealSequencesSectionsEquiv S x n)).choose)

@[simp]
lemma productRealIntApprox_apply_coord (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) (n : ℕ) :
    productIntLocallyConstantSectionsEquiv S (productRealIntApprox S x) n =
      (exists_locallyConstant_int_approx S (productRealSequencesSectionsEquiv S x n)).choose := by
  dsimp [productRealIntApprox]
  exact congrFun (LinearEquiv.apply_symm_apply (productIntLocallyConstantSectionsEquiv S)
    (fun n => (exists_locallyConstant_int_approx S (productRealSequencesSectionsEquiv S x n)).choose)) n

/-- The uniformly bounded real correction term after subtracting the chosen integer
approximation. -/
noncomputable def productRealBoundedCorrection (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) : boundedRealSequences.obj.obj ⟨S⟩ :=
  (show BoundedRealSeqSection S from {
    val := fun n => productRealSequencesSectionsEquiv S x n -
      locallyConstantIntToRealLinear S
        (productIntLocallyConstantSectionsEquiv S (productRealIntApprox S x) n)
    isBounded := by
      refine ⟨2, ?_⟩
      intro s n
      rw [ContinuousMap.sub_apply]
      rw [locallyConstantIntToRealLinear_apply, productRealIntApprox_apply_coord]
      exact (exists_locallyConstant_int_approx S (productRealSequencesSectionsEquiv S x n)).choose_spec s })

@[simp]
lemma productRealBoundedCorrection_apply_coord (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) (n : ℕ) :
    (boundedRealSequencesSectionsEquiv S (productRealBoundedCorrection S x)).1 n =
      productRealSequencesSectionsEquiv S x n -
        locallyConstantIntToRealLinear S
          (productIntLocallyConstantSectionsEquiv S (productRealIntApprox S x) n) :=
  rfl

end ProjectiveGeneratorProof
end Solid
end LightCondensed
