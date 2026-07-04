module

public import LeanCondensed.Projects.SolidProjectiveGenerator.RealSequences
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Abelian.CommSq
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

/-- Every real number is within distance `1 / 2` of an integer. -/
lemma exists_int_abs_sub_le_half (x : ℝ) :
    ∃ z : ℤ, |x - (z : ℝ)| ≤ (1 / 2 : ℝ) := by
  let z : ℤ := ⌊x + (1 / 2 : ℝ)⌋
  refine ⟨z, ?_⟩
  have hfloor_le : (z : ℝ) ≤ x + (1 / 2 : ℝ) := Int.floor_le _
  have hlt : x + (1 / 2 : ℝ) < (z : ℝ) + 1 := Int.lt_floor_add_one _
  have hleft : -(1 / 2 : ℝ) ≤ x - (z : ℝ) := by linarith
  have hright : x - (z : ℝ) ≤ (1 / 2 : ℝ) := by linarith
  exact abs_le.mpr ⟨hleft, hright⟩

/-- Every continuous real-valued function on a light profinite space is within distance `1` of a
locally constant integer-valued function. -/
lemma exists_locallyConstant_int_approx (S : LightProfinite) (f : C(S, ℝ)) :
    ∃ g : LocallyConstant S ℤ, ∀ s : S, ‖f s - (g s : ℝ)‖ ≤ (1 : ℝ) := by
  let R : Set (ℝ × ℝ) := {p | |p.1 - p.2| < (1 / 2 : ℝ)}
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
  let z : Fin n → ℤ := fun i => (exists_int_abs_sub_le_half (hval i)).choose
  let g : LocallyConstant S ℤ := idxLC.map z
  refine ⟨g, ?_⟩
  intro s
  have hdist : |f s - hval (idx s)| < (1 / 2 : ℝ) := happrox s
  have hnear : |hval (idx s) - (z (idx s) : ℝ)| ≤ (1 / 2 : ℝ) :=
    (exists_int_abs_sub_le_half (hval (idx s))).choose_spec
  change ‖f s - (z (idx s) : ℝ)‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs]
  calc
    |f s - (z (idx s) : ℝ)| =
        |(f s - hval (idx s)) + (hval (idx s) - (z (idx s) : ℝ))| := by ring_nf
    _ ≤ |f s - hval (idx s)| + |hval (idx s) - (z (idx s) : ℝ)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_le_add hdist.le hnear
    _ = (1 : ℝ) := by norm_num

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
      refine ⟨1, ?_⟩
      intro s n
      rw [ContinuousMap.sub_apply]
      rw [locallyConstantIntToRealLinear_apply, productRealIntApprox_apply_coord]
      simpa only [Nat.cast_one] using
        (exists_locallyConstant_int_approx S (productRealSequencesSectionsEquiv S x n)).choose_spec s })

@[simp]
lemma productRealBoundedCorrection_apply_coord (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) (n : ℕ) :
    (boundedRealSequencesSectionsEquiv S (productRealBoundedCorrection S x)).1 n =
      productRealSequencesSectionsEquiv S x n -
        locallyConstantIntToRealLinear S
          (productIntLocallyConstantSectionsEquiv S (productRealIntApprox S x) n) :=
  rfl

/-- The coordinatewise cast square from bounded integer sequences to all real sequences commutes. -/
@[reassoc (attr := simp)]
lemma boundedIntToBoundedReal_comp_boundedRealToProductReal :
    boundedIntToBoundedReal ≫ boundedRealToProductReal =
      boundedToProduct ≫ productIntToProductReal := by
  ext S x
  apply (productRealSequencesSectionsEquiv S.unop).injective
  ext n s
  change (productRealSequencesSectionsEquiv S.unop
      ((boundedRealToProductReal.hom.app S) ((boundedIntToBoundedReal.hom.app S) x)) n) s =
    (productRealSequencesSectionsEquiv S.unop
      ((productIntToProductReal.hom.app S) ((boundedToProduct.hom.app S) x)) n) s
  rw [boundedRealToProductReal_apply_coord, boundedIntToBoundedReal_apply_coord,
    productIntToProductReal_apply_coord, boundedToProduct_apply_coord]

/-- Every real product section is the sum of its chosen integer approximation and the uniformly
bounded real correction term. -/
lemma productRealIntApprox_add_correction (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) :
    x = (productIntToProductReal.hom.app ⟨S⟩) (productRealIntApprox S x) +
      (boundedRealToProductReal.hom.app ⟨S⟩) (productRealBoundedCorrection S x) := by
  apply (productRealSequencesSectionsEquiv S).injective
  ext n s
  rw [(productRealSequencesSectionsEquiv S).map_add]
  change (productRealSequencesSectionsEquiv S x n) s =
      (productRealSequencesSectionsEquiv S
          ((productIntToProductReal.hom.app ⟨S⟩) (productRealIntApprox S x)) n) s +
        (productRealSequencesSectionsEquiv S
          ((boundedRealToProductReal.hom.app ⟨S⟩) (productRealBoundedCorrection S x)) n) s
  rw [productIntToProductReal_apply_coord, boundedRealToProductReal_apply_coord,
    productRealBoundedCorrection_apply_coord]
  simp

/-- If an integer product section becomes a bounded real section after coordinatewise casting, then
it already comes from a bounded integer sequence section. -/
lemma exists_boundedInt_of_productIntToProductReal_eq_boundedReal (S : LightProfinite)
    (y : productIntLight.obj.obj ⟨S⟩) (b : boundedRealSequences.obj.obj ⟨S⟩)
    (h : (productIntToProductReal.hom.app ⟨S⟩) y =
      (boundedRealToProductReal.hom.app ⟨S⟩) b) :
    ∃ a : boundedIntSequences.obj.obj ⟨S⟩,
      (boundedToProduct.hom.app ⟨S⟩) a = y ∧
        (boundedIntToBoundedReal.hom.app ⟨S⟩) a = b := by
  obtain ⟨N, hN⟩ := (boundedRealSequencesSectionsEquiv S b).2
  let aSec : BoundedIntSeqSection S := {
    val := productIntLocallyConstantSectionsEquiv S y
    isBounded := by
      refine ⟨N, ?_⟩
      intro s n
      have hcoord := congrArg (fun x => productRealSequencesSectionsEquiv S x n) h
      rw [productIntToProductReal_apply_coord, boundedRealToProductReal_apply_coord] at hcoord
      have hp := congrArg (fun f : C(S, ℝ) => f s) hcoord
      have hb : ‖((productIntLocallyConstantSectionsEquiv S y n s : ℤ) : ℝ)‖ ≤ (N : ℝ) := by
        change ‖(locallyConstantIntToRealLinear S
          (productIntLocallyConstantSectionsEquiv S y n)) s‖ ≤ (N : ℝ)
        rw [hp]
        exact hN s n
      rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs] at hb
      exact_mod_cast hb }
  let a : boundedIntSequences.obj.obj ⟨S⟩ := aSec
  refine ⟨a, ?_, ?_⟩
  · apply (productIntLocallyConstantSectionsEquiv S).injective
    ext n
    rw [boundedToProduct_apply_coord]
    rfl
  · apply BoundedRealSeqSection.ext_apply
    intro n s
    have hcoord := congrArg (fun x => productRealSequencesSectionsEquiv S x n) h
    rw [productIntToProductReal_apply_coord, boundedRealToProductReal_apply_coord] at hcoord
    have hp := congrArg (fun f : C(S, ℝ) => f s) hcoord
    change (((aSec.val n s : ℤ) : ℝ)) = (show BoundedRealSeqSection S from b).val n s
    simpa [aSec, locallyConstantIntToRealLinear_apply] using hp

/-- The sectionwise lift into bounded integer sequences for a cone over the integer/real cast
square. -/
noncomputable def boundedIntPullbackLiftSection {W : LightCondAb}
    (fst : W ⟶ productIntLight) (snd : W ⟶ boundedRealSequences)
    (h : fst ≫ productIntToProductReal = snd ≫ boundedRealToProductReal)
    (S : LightProfinite) (w : W.obj.obj ⟨S⟩) : BoundedIntSeqSection S where
  val := productIntLocallyConstantSectionsEquiv S ((fst.hom.app ⟨S⟩) w)
  isBounded := by
    obtain ⟨N, hN⟩ := (boundedRealSequencesSectionsEquiv S ((snd.hom.app ⟨S⟩) w)).2
    refine ⟨N, ?_⟩
    intro s n
    have happ := congrArg (fun e : W ⟶ productRealSequences => e.hom.app ⟨S⟩ w) h
    change (productIntToProductReal.hom.app ⟨S⟩ ((fst.hom.app ⟨S⟩) w)) =
      (boundedRealToProductReal.hom.app ⟨S⟩ ((snd.hom.app ⟨S⟩) w)) at happ
    have hcoord := congrArg (fun x => productRealSequencesSectionsEquiv S x n) happ
    rw [productIntToProductReal_apply_coord, boundedRealToProductReal_apply_coord] at hcoord
    have hp := congrArg (fun f : C(S, ℝ) => f s) hcoord
    have hb : ‖((productIntLocallyConstantSectionsEquiv S ((fst.hom.app ⟨S⟩) w) n s : ℤ) : ℝ)‖ ≤ (N : ℝ) := by
      change ‖(locallyConstantIntToRealLinear S
        (productIntLocallyConstantSectionsEquiv S ((fst.hom.app ⟨S⟩) w) n)) s‖ ≤ (N : ℝ)
      rw [hp]
      exact hN s n
    rw [Real.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs] at hb
    exact_mod_cast hb

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The lift from a cone over the cast square to bounded integer sequences. -/
noncomputable def boundedIntPullbackLift {W : LightCondAb}
    (fst : W ⟶ productIntLight) (snd : W ⟶ boundedRealSequences)
    (h : fst ≫ productIntToProductReal = snd ≫ boundedRealToProductReal) :
    W ⟶ boundedIntSequences where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun w => boundedIntPullbackLiftSection fst snd h S.unop w
      map_add' := by
        intro x y
        apply BoundedIntSeqSection.ext_apply
        intro n s
        change (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) (x + y)) n) s =
          (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) x) n) s +
            (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) y) n) s
        rw [map_add, map_add]
        rfl
      map_smul' := by
        intro a x
        apply BoundedIntSeqSection.ext_apply
        intro n s
        dsimp [boundedIntPullbackLiftSection]
        have hfstp := congrArg
          (fun y : productIntLight.obj.obj S =>
            (productIntLocallyConstantSectionsEquiv S.unop y n) s)
          ((fst.hom.app S).hom.map_smul a x)
        have hlinp := congrArg (fun f : LocallyConstant S.unop ℤ => f s)
          (congrFun ((productIntLocallyConstantSectionsEquiv S.unop).map_smul a
            ((fst.hom.app S) x)) n)
        exact hfstp.trans hlinp }
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext w
      apply BoundedIntSeqSection.ext_apply
      intro n t
      change (productIntLocallyConstantSectionsEquiv T.unop
          ((fst.hom.app T) (W.obj.map φ w)) n) t =
        (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) w) n) (φ.unop t)
      rw [LightCondMod.hom_naturality_apply ℤ fst φ w]
      change (productIntLocallyConstantSectionsEquiv T.unop
          (productIntLight.obj.map (φ.unop.op) ((fst.hom.app S) w)) n) t =
        (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) w) n) (φ.unop t)
      rw [productIntLocallyConstantSectionsEquiv_map (φ := φ.unop)]
      rfl }

@[reassoc (attr := simp)]
lemma boundedIntPullbackLift_fac_left {W : LightCondAb}
    (fst : W ⟶ productIntLight) (snd : W ⟶ boundedRealSequences)
    (h : fst ≫ productIntToProductReal = snd ≫ boundedRealToProductReal) :
    boundedIntPullbackLift fst snd h ≫ boundedToProduct = fst := by
  ext S w
  apply (productIntLocallyConstantSectionsEquiv S.unop).injective
  ext n s
  change (productIntLocallyConstantSectionsEquiv S.unop
      ((boundedToProduct.hom.app S) ((boundedIntPullbackLift fst snd h).hom.app S w)) n) s =
    (productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) w) n) s
  rw [boundedToProduct_apply_coord]
  rfl

@[reassoc (attr := simp)]
lemma boundedIntPullbackLift_fac_right {W : LightCondAb}
    (fst : W ⟶ productIntLight) (snd : W ⟶ boundedRealSequences)
    (h : fst ≫ productIntToProductReal = snd ≫ boundedRealToProductReal) :
    boundedIntPullbackLift fst snd h ≫ boundedIntToBoundedReal = snd := by
  ext S w
  apply BoundedRealSeqSection.ext_apply
  intro n s
  have happ := congrArg (fun e : W ⟶ productRealSequences => e.hom.app S w) h
  change (productIntToProductReal.hom.app S ((fst.hom.app S) w)) =
    (boundedRealToProductReal.hom.app S ((snd.hom.app S) w)) at happ
  have hcoord := congrArg (fun x => productRealSequencesSectionsEquiv S.unop x n) happ
  rw [productIntToProductReal_apply_coord, boundedRealToProductReal_apply_coord] at hcoord
  have hp := congrArg (fun f : C(S.unop, ℝ) => f s) hcoord
  change (((productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) w) n s : ℤ) : ℝ)) =
    ((boundedRealSequencesSectionsEquiv S.unop ((snd.hom.app S) w)).1 n) s
  simpa [boundedIntPullbackLift, boundedIntPullbackLiftSection,
    locallyConstantIntToRealLinear_apply] using hp

lemma boundedIntPullbackLift_unique {W : LightCondAb}
    (fst : W ⟶ productIntLight) (snd : W ⟶ boundedRealSequences)
    (h : fst ≫ productIntToProductReal = snd ≫ boundedRealToProductReal)
    (m : W ⟶ boundedIntSequences) (hm_left : m ≫ boundedToProduct = fst) :
    m = boundedIntPullbackLift fst snd h := by
  ext S w
  apply BoundedIntSeqSection.ext_apply
  intro n s
  have hcoord := congrArg (fun e : W ⟶ productIntLight => e.hom.app S w) hm_left
  change (boundedToProduct.hom.app S ((m.hom.app S) w)) = (fst.hom.app S w) at hcoord
  have hn := congrArg (fun x => productIntLocallyConstantSectionsEquiv S.unop x n) hcoord
  rw [boundedToProduct_apply_coord] at hn
  change (boundedIntSequencesSectionsEquiv S.unop ((m.hom.app S) w)).val n s =
    productIntLocallyConstantSectionsEquiv S.unop ((fst.hom.app S) w) n s
  exact congrArg (fun f : LocallyConstant S.unop ℤ => f s) hn

/-- The square of bounded integer sequences, all integer sequences, bounded real sequences, and all
real sequences is a pullback. -/
lemma boundedInt_real_pullback :
    IsPullback boundedToProduct boundedIntToBoundedReal
      productIntToProductReal boundedRealToProductReal := by
  refine IsPullback.mk (CommSq.mk ?_) ⟨?_⟩
  · exact boundedIntToBoundedReal_comp_boundedRealToProductReal.symm
  · refine PullbackCone.IsLimit.mk _ (fun s => boundedIntPullbackLift s.fst s.snd s.condition) ?_ ?_ ?_
    · intro s
      exact boundedIntPullbackLift_fac_left s.fst s.snd s.condition
    · intro s
      exact boundedIntPullbackLift_fac_right s.fst s.snd s.condition
    · intro s m hm₁ _hm₂
      exact boundedIntPullbackLift_unique s.fst s.snd s.condition m hm₁

/-- The quotient comparison map induced by the commuting cast square. -/
noncomputable def productIntQuotientToRealQuotient :
    cokernel boundedToProduct ⟶ cokernel boundedRealToProductReal :=
  cokernel.map boundedToProduct boundedRealToProductReal boundedIntToBoundedReal
    productIntToProductReal boundedIntToBoundedReal_comp_boundedRealToProductReal.symm

@[reassoc (attr := simp)]
lemma productIntQuotientToRealQuotient_π :
    cokernel.π boundedToProduct ≫ productIntQuotientToRealQuotient =
      productIntToProductReal ≫ cokernel.π boundedRealToProductReal := by
  dsimp [productIntQuotientToRealQuotient]
  rw [cokernel.π_desc]

lemma epi_productIntToProductReal_cokernelπ :
    Epi (productIntToProductReal ≫ cokernel.π boundedRealToProductReal) := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro S q
  have hπepi : Epi (cokernel.π boundedRealToProductReal) := inferInstance
  have hloc := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite ℤ
    (cokernel.π boundedRealToProductReal)).mp hπepi
  obtain ⟨S', φ, hφ, x, hx⟩ := hloc S q
  refine ⟨S', φ, hφ, productRealIntApprox S' x, ?_⟩
  have hdecomp := productRealIntApprox_add_correction S' x
  calc
    ((productIntToProductReal ≫ cokernel.π boundedRealToProductReal).hom.app ⟨S'⟩)
        (productRealIntApprox S' x)
        = (cokernel.π boundedRealToProductReal).hom.app ⟨S'⟩
          ((productIntToProductReal.hom.app ⟨S'⟩) (productRealIntApprox S' x)) := rfl
    _ = (cokernel.π boundedRealToProductReal).hom.app ⟨S'⟩ x := by
      conv_rhs => rw [hdecomp]
      rw [map_add]
      have hzero : (cokernel.π boundedRealToProductReal).hom.app ⟨S'⟩
          ((boundedRealToProductReal.hom.app ⟨S'⟩) (productRealBoundedCorrection S' x)) = 0 := by
        change ((boundedRealToProductReal ≫ cokernel.π boundedRealToProductReal).hom.app ⟨S'⟩)
          (productRealBoundedCorrection S' x) = 0
        rw [cokernel.condition]
        rfl
      simp [hzero]
    _ = (cokernel boundedRealToProductReal).obj.map φ.op q := hx

instance productIntQuotientToRealQuotient_epi : Epi productIntQuotientToRealQuotient := by
  haveI : Epi (cokernel.π boundedToProduct ≫ productIntQuotientToRealQuotient) := by
    rw [productIntQuotientToRealQuotient_π]
    exact epi_productIntToProductReal_cokernelπ
  exact epi_of_epi (cokernel.π boundedToProduct) productIntQuotientToRealQuotient

instance productIntQuotientToRealQuotient_mono : Mono productIntQuotientToRealQuotient := by
  dsimp [productIntQuotientToRealQuotient]
  exact CategoryTheory.Abelian.mono_cokernel_map_of_isPullback boundedInt_real_pullback

instance productIntQuotientToRealQuotient_isIso : IsIso productIntQuotientToRealQuotient :=
  isIso_of_mono_of_epi productIntQuotientToRealQuotient

/-- The integer quotient by bounded integer sequences agrees with the real quotient by bounded real
sequences. -/
noncomputable def productIntQuotientIsoRealQuotient :
    cokernel boundedToProduct ≅ cokernel boundedRealToProductReal :=
  asIso productIntQuotientToRealQuotient

end ProjectiveGeneratorProof
end Solid
end LightCondensed
