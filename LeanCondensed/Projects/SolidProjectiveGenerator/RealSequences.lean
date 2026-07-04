module

public import LeanCondensed.Projects.SolidProjectiveGenerator.BoundedSequences

@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The light condensed abelian group represented by the usual topological real line, regarded as
an additive topological `ℤ`-module. -/
noncomputable def realCondensedAb : LightCondAb :=
  LightCondensed.topModuleToLightCondAbObj LightCondAb.realTopModule

/-- Sections of `realCondensedAb` are continuous real-valued functions. -/
noncomputable def realCondensedAbSectionsEquiv (S : LightProfinite) :
    realCondensedAb.obj.obj ⟨S⟩ ≃ₗ[ℤ] C(S, ℝ) :=
  LinearEquiv.refl ℤ _

@[simp]
lemma realCondensedAbSectionsEquiv_map {S T : LightProfinite} (f : T ⟶ S)
    (x : realCondensedAb.obj.obj ⟨S⟩) :
    realCondensedAbSectionsEquiv T (realCondensedAb.obj.map f.op x) =
      (realCondensedAbSectionsEquiv S x).comp f.hom.hom :=
  rfl

/-- The light condensed abelian group of all real-valued sequences. -/
noncomputable def productRealSequences : LightCondAb :=
  ∏ᶜ fun _ : ℕ => realCondensedAb

/-- Sections of a countable product of copies of `realCondensedAb` are countable products of
sections. -/
noncomputable def productRealRawSectionsEquiv (S : LightProfinite) :
    productRealSequences.obj.obj ⟨S⟩ ≃ₗ[ℤ]
      (∀ _ : ℕ, realCondensedAb.obj.obj ⟨S⟩) := by
  let evS : LightCondAb ⥤ ModuleCat ℤ :=
    sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ) ⋙
      (evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj ⟨S⟩
  let e := PreservesProduct.iso evS (fun _ : ℕ => realCondensedAb) ≪≫
    ModuleCat.piIsoPi (fun _ : ℕ => evS.obj realCondensedAb)
  let coord : productRealSequences.obj.obj ⟨S⟩ →
      (∀ _ : ℕ, realCondensedAb.obj.obj ⟨S⟩) :=
    fun x n => (Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩ x
  have hcoord : ∀ x, e.hom x = coord x := by
    intro x
    ext n
    letI : Module ℤ (∀ _ : ℕ, evS.obj realCondensedAb) :=
      Pi.module ℕ (fun _ : ℕ => evS.obj realCondensedAb) ℤ
    change (((PreservesProduct.iso evS (fun _ : ℕ => realCondensedAb)).hom ≫
      (ModuleCat.piIsoPi (fun _ : ℕ => evS.obj realCondensedAb)).hom) ≫ ModuleCat.ofHom
        (LinearMap.proj n : (∀ _ : ℕ, evS.obj realCondensedAb) →ₗ[ℤ]
          evS.obj realCondensedAb)).hom x =
      (Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩ x
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    change ((PreservesProduct.iso evS (fun _ : ℕ => realCondensedAb)).hom ≫
      Pi.π (fun _ : ℕ => evS.obj realCondensedAb) n).hom x =
      (Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩ x
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
    rfl
  let a : productRealSequences.obj.obj ⟨S⟩ ≃+
      (∀ _ : ℕ, realCondensedAb.obj.obj ⟨S⟩) := {
    toFun := coord
    invFun := fun y => e.inv y
    left_inv := by
      intro x
      change e.inv (coord x) = x
      rw [← hcoord x]
      change (e.hom ≫ e.inv).hom x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := by
      intro y
      change coord (e.inv y) = y
      rw [← hcoord (e.inv y)]
      change (e.inv ≫ e.hom).hom y = y
      rw [e.inv_hom_id]
      rfl
    map_add' := by
      intro x y
      ext n
      exact ((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩).hom.map_add x y }
  exact a.toIntLinearEquiv

/-- Sections of `productRealSequences` as countable sequences of continuous real-valued functions. -/
noncomputable def productRealSequencesSectionsEquiv (S : LightProfinite) :
    productRealSequences.obj.obj ⟨S⟩ ≃ₗ[ℤ] (ℕ → C(S, ℝ)) :=
  (productRealRawSectionsEquiv S).trans
    (LinearEquiv.piCongrRight fun _ : ℕ => realCondensedAbSectionsEquiv S)

@[simp]
lemma productRealSequencesSectionsEquiv_apply (S : LightProfinite)
    (x : productRealSequences.obj.obj ⟨S⟩) (n : ℕ) :
    productRealSequencesSectionsEquiv S x n =
      realCondensedAbSectionsEquiv S
        ((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩ x) :=
  rfl

@[simp]
lemma productRealSequencesSectionsEquiv_symm_apply (S : LightProfinite)
    (x : ℕ → C(S, ℝ)) (n : ℕ) :
    realCondensedAbSectionsEquiv S
      (((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩)
        ((productRealSequencesSectionsEquiv S).symm x)) = x n := by
  have h := congrFun (LinearEquiv.apply_symm_apply (productRealSequencesSectionsEquiv S) x) n
  rw [productRealSequencesSectionsEquiv_apply] at h
  exact h

lemma productRealRawSectionsEquiv_map {S T : LightProfinite} (f : T ⟶ S)
    (x : productRealSequences.obj.obj ⟨S⟩) :
    productRealRawSectionsEquiv T (productRealSequences.obj.map f.op x) =
      fun n : ℕ => realCondensedAb.obj.map f.op (productRealRawSectionsEquiv S x n) := by
  ext n
  rw [show productRealRawSectionsEquiv T (productRealSequences.obj.map f.op x) n =
      ((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨T⟩)
        (productRealSequences.obj.map f.op x) by rfl]
  rw [show productRealRawSectionsEquiv S x n =
      ((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩) x by rfl]
  exact LightCondMod.hom_naturality_apply ℤ (Pi.π (fun _ : ℕ => realCondensedAb) n) f.op x

@[simp]
lemma productRealSequencesSectionsEquiv_map {S T : LightProfinite} (f : T ⟶ S)
    (x : productRealSequences.obj.obj ⟨S⟩) :
    productRealSequencesSectionsEquiv T (productRealSequences.obj.map f.op x) =
      fun n : ℕ => (productRealSequencesSectionsEquiv S x n).comp f.hom.hom := by
  ext n t
  rw [productRealSequencesSectionsEquiv_apply, productRealSequencesSectionsEquiv_apply]
  rw [← realCondensedAbSectionsEquiv_map f
    (((Pi.π (fun _ : ℕ => realCondensedAb) n).hom.app ⟨S⟩) x)]
  exact congrArg (fun g : C(T, ℝ) => g t) (congrArg (realCondensedAbSectionsEquiv T)
    (LightCondMod.hom_naturality_apply ℤ (Pi.π (fun _ : ℕ => realCondensedAb) n) f.op x))

/-- Uniformly bounded sequences of continuous real-valued functions on a light profinite space.  The
bound is uniform both in the source point and in the sequence coordinate. -/
structure BoundedRealSeqSection (S : LightProfinite) where
  val : ℕ → C(S, ℝ)
  isBounded : ∃ N : ℕ, ∀ s : S, ∀ n : ℕ, ‖val n s‖ ≤ (N : ℝ)

namespace BoundedRealSeqSection

@[ext]
lemma ext {S : LightProfinite} {x y : BoundedRealSeqSection S}
    (h : ∀ n : ℕ, x.val n = y.val n) : x = y := by
  cases x
  cases y
  simp only at h
  congr
  exact funext h

lemma ext_apply {S : LightProfinite} {x y : BoundedRealSeqSection S}
    (h : ∀ n : ℕ, ∀ s : S, x.val n s = y.val n s) : x = y := by
  apply ext
  intro n
  exact ContinuousMap.ext (h n)

instance (S : LightProfinite) : Zero (BoundedRealSeqSection S) where
  zero := {
    val := 0
    isBounded := by
      refine ⟨0, ?_⟩
      intro s n
      simp }

instance (S : LightProfinite) : Add (BoundedRealSeqSection S) where
  add x y := {
    val := fun n => x.val n + y.val n
    isBounded := by
      obtain ⟨Nx, hx⟩ := x.isBounded
      obtain ⟨Ny, hy⟩ := y.isBounded
      refine ⟨Nx + Ny, ?_⟩
      intro s n
      calc
        ‖(x.val n + y.val n) s‖ ≤ ‖x.val n s‖ + ‖y.val n s‖ := norm_add_le _ _
        _ ≤ (Nx : ℝ) + (Ny : ℝ) := add_le_add (hx s n) (hy s n)
        _ = (Nx + Ny : ℕ) := by norm_num }

instance (S : LightProfinite) : Neg (BoundedRealSeqSection S) where
  neg x := {
    val := fun n => -x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨N, ?_⟩
      intro s n
      simpa using hN s n }

instance (S : LightProfinite) : Sub (BoundedRealSeqSection S) where
  sub x y := {
    val := fun n => x.val n - y.val n
    isBounded := by
      obtain ⟨Nx, hx⟩ := x.isBounded
      obtain ⟨Ny, hy⟩ := y.isBounded
      refine ⟨Nx + Ny, ?_⟩
      intro s n
      calc
        ‖(x.val n - y.val n) s‖ ≤ ‖x.val n s‖ + ‖y.val n s‖ := norm_sub_le _ _
        _ ≤ (Nx : ℝ) + (Ny : ℝ) := add_le_add (hx s n) (hy s n)
        _ = (Nx + Ny : ℕ) := by norm_num }

instance (S : LightProfinite) : SMul ℕ (BoundedRealSeqSection S) where
  smul m x := {
    val := fun n => m • x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨m * N, ?_⟩
      intro s n
      calc
        ‖(m • x.val n) s‖ = ‖(m : ℝ) * x.val n s‖ := by simp [nsmul_eq_mul]
        _ = (m : ℝ) * ‖x.val n s‖ := by simp
        _ ≤ (m : ℝ) * (N : ℝ) := by
          exact mul_le_mul_of_nonneg_left (hN s n) (Nat.cast_nonneg m)
        _ = (m * N : ℕ) := by norm_num }

instance (S : LightProfinite) : SMul ℤ (BoundedRealSeqSection S) where
  smul a x := {
    val := fun n => a • x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨Int.natAbs a * N, ?_⟩
      intro s n
      calc
        ‖(a • x.val n) s‖ = (Int.natAbs a : ℝ) * ‖x.val n s‖ := by simp
        _ ≤ (Int.natAbs a : ℝ) * (N : ℝ) := by
          exact mul_le_mul_of_nonneg_left (hN s n) (Nat.cast_nonneg (Int.natAbs a))
        _ = (Int.natAbs a * N : ℕ) := by norm_num }

instance (S : LightProfinite) : AddCommGroup (BoundedRealSeqSection S) :=
  Function.Injective.addCommGroup (fun x : BoundedRealSeqSection S => x.val)
    (fun _ _ h => ext (fun n => congrFun h n)) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance (S : LightProfinite) : Module ℤ (BoundedRealSeqSection S) :=
  AddCommGroup.toIntModule (BoundedRealSeqSection S)

abbrev SubtypeForm (S : LightProfinite) :=
  { x : ℕ → C(S, ℝ) // ∃ N : ℕ, ∀ s n, ‖x n s‖ ≤ (N : ℝ) }

instance (S : LightProfinite) : Zero (SubtypeForm S) where
  zero := ⟨(0 : ℕ → C(S, ℝ)), (0 : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : Add (SubtypeForm S) where
  add x y := ⟨(⟨x.1, x.2⟩ + ⟨y.1, y.2⟩ : BoundedRealSeqSection S).val,
    (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩ : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : Neg (SubtypeForm S) where
  neg x := ⟨(-⟨x.1, x.2⟩ : BoundedRealSeqSection S).val,
    (-⟨x.1, x.2⟩ : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : Sub (SubtypeForm S) where
  sub x y := ⟨(⟨x.1, x.2⟩ - ⟨y.1, y.2⟩ : BoundedRealSeqSection S).val,
    (⟨x.1, x.2⟩ - ⟨y.1, y.2⟩ : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : SMul ℕ (SubtypeForm S) where
  smul m x := ⟨(m • ⟨x.1, x.2⟩ : BoundedRealSeqSection S).val,
    (m • ⟨x.1, x.2⟩ : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : SMul ℤ (SubtypeForm S) where
  smul a x := ⟨(a • ⟨x.1, x.2⟩ : BoundedRealSeqSection S).val,
    (a • ⟨x.1, x.2⟩ : BoundedRealSeqSection S).isBounded⟩

instance (S : LightProfinite) : AddCommGroup (SubtypeForm S) :=
  Function.Injective.addCommGroup (fun x : SubtypeForm S => x.1)
    (fun _ _ h => Subtype.ext h) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance (S : LightProfinite) : Module ℤ (SubtypeForm S) :=
  AddCommGroup.toIntModule (SubtypeForm S)

/-- The structure form of bounded real sequence sections is equivalent to the subtype form used in
quotient-comparison statements. -/
noncomputable def subtypeLinearEquiv (S : LightProfinite) :
    BoundedRealSeqSection S ≃ₗ[ℤ] SubtypeForm S := by
  let e : BoundedRealSeqSection S ≃+ SubtypeForm S := {
    toFun := fun x => ⟨x.val, x.isBounded⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; cases x; rfl
    map_add' := by intro x y; rfl }
  exact e.toIntLinearEquiv

@[simp]
lemma subtypeLinearEquiv_apply_coe (S : LightProfinite) (x : BoundedRealSeqSection S) :
    ((subtypeLinearEquiv S x).1 : ℕ → C(S, ℝ)) = x.val :=
  rfl

@[simp]
lemma val_zero (S : LightProfinite) (n : ℕ) :
    (0 : BoundedRealSeqSection S).val n = 0 :=
  rfl

@[simp]
lemma val_add {S : LightProfinite} (x y : BoundedRealSeqSection S) (n : ℕ) :
    (x + y).val n = x.val n + y.val n :=
  rfl

@[simp]
lemma val_neg {S : LightProfinite} (x : BoundedRealSeqSection S) (n : ℕ) :
    (-x).val n = -x.val n :=
  rfl

@[simp]
lemma val_sub {S : LightProfinite} (x y : BoundedRealSeqSection S) (n : ℕ) :
    (x - y).val n = x.val n - y.val n :=
  rfl

@[simp]
lemma val_zsmul {S : LightProfinite} (a : ℤ) (x : BoundedRealSeqSection S) (n : ℕ) :
    (a • x).val n = a • x.val n :=
  rfl

end BoundedRealSeqSection

/-- Restrict a bounded real sequence section along a map of light profinite spaces. -/
def boundedRealSeqSectionComap {S T : LightProfinite} (f : T ⟶ S)
    (x : BoundedRealSeqSection S) : BoundedRealSeqSection T where
  val n := (x.val n).comp f.hom.hom
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    exact ⟨N, fun t n => hN (f t) n⟩

@[simp]
lemma boundedRealSeqSectionComap_val {S T : LightProfinite} (f : T ⟶ S)
    (x : BoundedRealSeqSection S) (n : ℕ) :
    (boundedRealSeqSectionComap f x).val n = (x.val n).comp f.hom.hom :=
  rfl

/-- The presheaf of uniformly bounded real sequences of continuous functions. -/
noncomputable def boundedRealSeqPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ where
  obj S := ModuleCat.of ℤ (BoundedRealSeqSection S.unop)
  map {S T} f := ModuleCat.ofHom {
    toFun := boundedRealSeqSectionComap f.unop
    map_add' := by
      intro x y
      ext n s
      rfl
    map_smul' := by
      intro a x
      ext n s
      rfl }
  map_id := by
    intro S
    ext x n s
    rfl
  map_comp := by
    intro S T U f g
    ext x n s
    rfl

@[simp]
lemma boundedRealSeqPresheaf_map_val {S T : LightProfinite} (f : T ⟶ S)
    (x : boundedRealSeqPresheaf.obj ⟨S⟩) (n : ℕ) :
    ((boundedRealSeqPresheaf.map f.op) x).val n = (x.val n).comp f.hom.hom :=
  rfl

noncomputable def descendContinuousReal {X B : LightProfinite} (π : X ⟶ B)
    [EffectiveEpi π] (c : PullbackCone π π) (hc : IsLimit c)
    (f : C(X, ℝ))
    (h : f.comp c.fst.hom.hom = f.comp c.snd.hom.hom) : C(B, ℝ) := by
  let xR : realCondensedAb.obj.obj ⟨X⟩ := (realCondensedAbSectionsEquiv X).symm f
  have hxR : ((forget ℤ).obj realCondensedAb).obj.map c.fst.op xR =
      ((forget ℤ).obj realCondensedAb).obj.map c.snd.op xR := by
    change realCondensedAb.obj.map c.fst.op xR = realCondensedAb.obj.map c.snd.op xR
    apply (realCondensedAbSectionsEquiv c.pt).injective
    rw [realCondensedAbSectionsEquiv_map, realCondensedAbSectionsEquiv_map]
    simp [xR, h]
  let target : {x : ((forget ℤ).obj realCondensedAb).obj.obj ⟨X⟩ |
      ((forget ℤ).obj realCondensedAb).obj.map c.fst.op x =
        ((forget ℤ).obj realCondensedAb).obj.map c.snd.op x} := ⟨xR, hxR⟩
  have hbij := (LightCondensed.equalizerCondition ((forget ℤ).obj realCondensedAb)).bijective_mapToEqualizer_pullback' c hc
  let y := Classical.choose (hbij.2 target)
  exact realCondensedAbSectionsEquiv B y

lemma descendContinuousReal_spec {X B : LightProfinite} (π : X ⟶ B)
    [EffectiveEpi π] (c : PullbackCone π π) (hc : IsLimit c)
    (f : C(X, ℝ))
    (h : f.comp c.fst.hom.hom = f.comp c.snd.hom.hom) :
    (descendContinuousReal π c hc f h).comp π.hom.hom = f := by
  dsimp [descendContinuousReal]
  let xR : realCondensedAb.obj.obj ⟨X⟩ := (realCondensedAbSectionsEquiv X).symm f
  have hxR : ((forget ℤ).obj realCondensedAb).obj.map c.fst.op xR =
      ((forget ℤ).obj realCondensedAb).obj.map c.snd.op xR := by
    change realCondensedAb.obj.map c.fst.op xR = realCondensedAb.obj.map c.snd.op xR
    apply (realCondensedAbSectionsEquiv c.pt).injective
    rw [realCondensedAbSectionsEquiv_map, realCondensedAbSectionsEquiv_map]
    simp [xR, h]
  let target : {x : ((forget ℤ).obj realCondensedAb).obj.obj ⟨X⟩ |
      ((forget ℤ).obj realCondensedAb).obj.map c.fst.op x =
        ((forget ℤ).obj realCondensedAb).obj.map c.snd.op x} := ⟨xR, hxR⟩
  have hbij := (LightCondensed.equalizerCondition ((forget ℤ).obj realCondensedAb)).bijective_mapToEqualizer_pullback' c hc
  let y := Classical.choose (hbij.2 target)
  have hy := Classical.choose_spec (hbij.2 target)
  have hy1 : ((forget ℤ).obj realCondensedAb).obj.map π.op y = xR := by
    have hval := congrArg Subtype.val hy
    change (((forget ℤ).obj realCondensedAb).obj.map π.op y) = xR at hval
    exact hval
  change realCondensedAbSectionsEquiv X (((forget ℤ).obj realCondensedAb).obj.map π.op y) = f
  rw [hy1]
  simp [xR]

lemma boundedRealSeqPresheaf_equalizerCondition_underlying :
    regularTopology.EqualizerCondition
      (boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := by
  apply regularTopology.EqualizerCondition.mk'
  intro X B π hπ c hc
  constructor
  · intro a b hab
    have hmap : boundedRealSeqPresheaf.map π.op a = boundedRealSeqPresheaf.map π.op b := by
      have hval := congrArg Subtype.val hab
      change (boundedRealSeqPresheaf.map π.op a) = boundedRealSeqPresheaf.map π.op b at hval
      exact hval
    apply BoundedRealSeqSection.ext_apply
    intro n s
    haveI : Epi π := inferInstance
    have hsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp inferInstance
    obtain ⟨x, hx⟩ := hsurj s
    have hcoord := congrArg (fun z : BoundedRealSeqSection X => z.val n) hmap
    have hpoint := congrArg (fun f : C(X, ℝ) => f x) hcoord
    change a.val n (π x) = b.val n (π x) at hpoint
    simpa [hx] using hpoint
  · intro target
    let yX : BoundedRealSeqSection X := target.1
    have compat : boundedRealSeqPresheaf.map c.fst.op yX =
        boundedRealSeqPresheaf.map c.snd.op yX := target.2
    let yB : BoundedRealSeqSection B := {
      val := fun n =>
        descendContinuousReal π c hc (yX.val n) (by
          have hcoord := congrArg (fun z : BoundedRealSeqSection c.pt => z.val n) compat
          simpa [boundedRealSeqPresheaf_map_val] using hcoord)
      isBounded := by
        obtain ⟨N, hN⟩ := yX.isBounded
        refine ⟨N, ?_⟩
        intro b n
        haveI : Epi π := inferInstance
        have hsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp inferInstance
        obtain ⟨x, hx⟩ := hsurj b
        have hspec := descendContinuousReal_spec π c hc (yX.val n) (by
          have hcoord := congrArg (fun z : BoundedRealSeqSection c.pt => z.val n) compat
          simpa [boundedRealSeqPresheaf_map_val] using hcoord)
        have hpoint := congrArg (fun f : C(X, ℝ) => f x) hspec
        change (descendContinuousReal π c hc (yX.val n) _ (π x)) = yX.val n x at hpoint
        rw [hx] at hpoint
        rw [hpoint]
        exact hN x n }
    refine ⟨yB, ?_⟩
    apply Subtype.ext
    apply BoundedRealSeqSection.ext
    intro n
    exact descendContinuousReal_spec π c hc (yX.val n) (by
      have hcoord := congrArg (fun z : BoundedRealSeqSection c.pt => z.val n) compat
      simpa [boundedRealSeqPresheaf_map_val] using hcoord)

instance uniqueRealSectionOfIsEmpty (S : LightProfinite) [IsEmpty S] :
    Unique (BoundedRealSeqSection S) where
  default := 0
  uniq x := by
    apply BoundedRealSeqSection.ext_apply
    intro n s
    exact isEmptyElim s

noncomputable def glueContinuousRealBinary {S T : LightProfiniteᵒᵖ}
    (xS : C(S.unop, ℝ)) (xT : C(T.unop, ℝ)) :
    C((S ⨯ T).unop, ℝ) := by
  let F := ((forget ℤ).obj realCondensedAb).obj
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv
      ((realCondensedAbSectionsEquiv S.unop).symm xS,
        (realCondensedAbSectionsEquiv T.unop).symm xT)
  exact realCondensedAbSectionsEquiv (S ⨯ T).unop (inv (prodComparison F S T) pair)

lemma glueContinuousRealBinary_fst {S T : LightProfiniteᵒᵖ}
    (xS : C(S.unop, ℝ)) (xT : C(T.unop, ℝ)) :
    (glueContinuousRealBinary xS xT).comp (prod.fst : S ⨯ T ⟶ S).unop.hom.hom = xS := by
  dsimp [glueContinuousRealBinary]
  let F := ((forget ℤ).obj realCondensedAb).obj
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv
      ((realCondensedAbSectionsEquiv S.unop).symm xS,
        (realCondensedAbSectionsEquiv T.unop).symm xT)
  rw [← realCondensedAbSectionsEquiv_map]
  have h := congrArg (fun f : F.obj S ⨯ F.obj T ⟶ F.obj S => f pair)
    (inv_prodComparison_map_fst (F := F) (A := S) (B := T))
  change realCondensedAbSectionsEquiv S.unop
      ((inv (prodComparison F S T) ≫ F.map (prod.fst : S ⨯ T ⟶ S)) pair) = xS
  rw [h]
  simp [pair]

lemma glueContinuousRealBinary_snd {S T : LightProfiniteᵒᵖ}
    (xS : C(S.unop, ℝ)) (xT : C(T.unop, ℝ)) :
    (glueContinuousRealBinary xS xT).comp (prod.snd : S ⨯ T ⟶ T).unop.hom.hom = xT := by
  dsimp [glueContinuousRealBinary]
  let F := ((forget ℤ).obj realCondensedAb).obj
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv
      ((realCondensedAbSectionsEquiv S.unop).symm xS,
        (realCondensedAbSectionsEquiv T.unop).symm xT)
  rw [← realCondensedAbSectionsEquiv_map]
  have h := congrArg (fun f : F.obj S ⨯ F.obj T ⟶ F.obj T => f pair)
    (inv_prodComparison_map_snd (F := F) (A := S) (B := T))
  change realCondensedAbSectionsEquiv T.unop
      ((inv (prodComparison F S T) ≫ F.map (prod.snd : S ⨯ T ⟶ T)) pair) = xT
  rw [h]
  simp [pair]

noncomputable def glueBoundedRealBinary {S T : LightProfiniteᵒᵖ}
    (xS : BoundedRealSeqSection S.unop) (xT : BoundedRealSeqSection T.unop) :
    BoundedRealSeqSection (S ⨯ T).unop where
  val n := glueContinuousRealBinary (xS.val n) (xT.val n)
  isBounded := by
    obtain ⟨NS, hS⟩ := xS.isBounded
    obtain ⟨NT, hT⟩ := xT.isBounded
    refine ⟨max NS NT, ?_⟩
    intro p n
    rcases binaryProduct_jointly_surjective (S := S) (T := T) p with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · have hfst := glueContinuousRealBinary_fst (S := S) (T := T) (xS.val n) (xT.val n)
      have hp := congrArg (fun f : C(S.unop, ℝ) => f s) hfst
      change (glueContinuousRealBinary (xS.val n) (xT.val n))
          ((prod.fst : S ⨯ T ⟶ S).unop s) = xS.val n s at hp
      rw [hp]
      exact le_trans (hS s n) (by exact_mod_cast Nat.le_max_left NS NT)
    · have hsnd := glueContinuousRealBinary_snd (S := S) (T := T) (xS.val n) (xT.val n)
      have hp := congrArg (fun f : C(T.unop, ℝ) => f t) hsnd
      change (glueContinuousRealBinary (xS.val n) (xT.val n))
          ((prod.snd : S ⨯ T ⟶ T).unop t) = xT.val n t at hp
      rw [hp]
      exact le_trans (hT t n) (by exact_mod_cast Nat.le_max_right NS NT)

lemma glueBoundedRealBinary_fst {S T : LightProfiniteᵒᵖ}
    (xS : BoundedRealSeqSection S.unop) (xT : BoundedRealSeqSection T.unop) :
    boundedRealSeqPresheaf.map (prod.fst : S ⨯ T ⟶ S) (glueBoundedRealBinary xS xT) = xS := by
  apply BoundedRealSeqSection.ext
  intro n
  exact glueContinuousRealBinary_fst (S := S) (T := T) (xS.val n) (xT.val n)

lemma glueBoundedRealBinary_snd {S T : LightProfiniteᵒᵖ}
    (xS : BoundedRealSeqSection S.unop) (xT : BoundedRealSeqSection T.unop) :
    boundedRealSeqPresheaf.map (prod.snd : S ⨯ T ⟶ T) (glueBoundedRealBinary xS xT) = xT := by
  apply BoundedRealSeqSection.ext
  intro n
  exact glueContinuousRealBinary_snd (S := S) (T := T) (xS.val n) (xT.val n)

instance boundedRealSeqPresheaf_prodComparison_isIso (S T : LightProfiniteᵒᵖ) :
    IsIso (prodComparison (boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) S T) := by
  apply (isIso_iff_bijective (prodComparison
    (boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) S T)).mpr
  constructor
  · intro a b hab
    apply BoundedRealSeqSection.ext_apply
    intro n p
    rcases binaryProduct_jointly_surjective (S := S) (T := T) p with ⟨s, hs⟩ | ⟨t, ht⟩
    · let F := boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
      have hfst : F.map (prod.fst : S ⨯ T ⟶ S) a = F.map (prod.fst : S ⨯ T ⟶ S) b := by
        have h := congrArg (fun q => (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) q) hab
        have ha := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f a)
          (prodComparison_fst F S T)
        have hb := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f b)
          (prodComparison_fst F S T)
        exact ha.symm.trans (h.trans hb)
      have hcoord := congrArg (fun z : BoundedRealSeqSection S.unop => z.val n) hfst
      have hp := congrArg (fun f : C(S.unop, ℝ) => f s) hcoord
      change a.val n ((prod.fst : S ⨯ T ⟶ S).unop s) =
        b.val n ((prod.fst : S ⨯ T ⟶ S).unop s) at hp
      simpa [hs] using hp
    · let F := boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
      have hsnd : F.map (prod.snd : S ⨯ T ⟶ T) a = F.map (prod.snd : S ⨯ T ⟶ T) b := by
        have h := congrArg (fun q => (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) q) hab
        have ha := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f a)
          (prodComparison_snd F S T)
        have hb := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f b)
          (prodComparison_snd F S T)
        exact ha.symm.trans (h.trans hb)
      have hcoord := congrArg (fun z : BoundedRealSeqSection T.unop => z.val n) hsnd
      have hp := congrArg (fun f : C(T.unop, ℝ) => f t) hcoord
      change a.val n ((prod.snd : S ⨯ T ⟶ T).unop t) =
        b.val n ((prod.snd : S ⨯ T ⟶ T).unop t) at hp
      simpa [ht] using hp
  · intro y
    let F := boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
    let xS : BoundedRealSeqSection S.unop := (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) y
    let xT : BoundedRealSeqSection T.unop := (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) y
    let g : F.obj (S ⨯ T) := glueBoundedRealBinary xS xT
    refine ⟨g, ?_⟩
    apply (Types.binaryProductIso (F.obj S) (F.obj T)).toEquiv.injective
    apply Prod.ext
    · change ((Types.binaryProductIso (F.obj S) (F.obj T)).hom
          (prodComparison F S T g)).1 = ((Types.binaryProductIso (F.obj S) (F.obj T)).hom y).1
      rw [Types.binaryProductIso_hom_comp_fst_apply,
        Types.binaryProductIso_hom_comp_fst_apply]
      have hcomp := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f g)
        (prodComparison_fst F S T)
      change (prodComparison F S T ≫ prod.fst) g =
        (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) y
      rw [hcomp]
      exact glueBoundedRealBinary_fst xS xT
    · change ((Types.binaryProductIso (F.obj S) (F.obj T)).hom
          (prodComparison F S T g)).2 = ((Types.binaryProductIso (F.obj S) (F.obj T)).hom y).2
      rw [Types.binaryProductIso_hom_comp_snd_apply,
        Types.binaryProductIso_hom_comp_snd_apply]
      have hcomp := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f g)
        (prodComparison_snd F S T)
      change (prodComparison F S T ≫ prod.snd) g =
        (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) y
      rw [hcomp]
      exact glueBoundedRealBinary_snd xS xT

instance boundedRealSeqPresheaf_preservesFiniteProducts_underlying :
    PreservesFiniteProducts (boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := by
  let F := boundedRealSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryProducts_of_isIso_prodComparison F
  haveI : PreservesLimitsOfShape (Discrete.{0} PEmpty) F := by
    haveI : IsEmpty ((⊤_ LightProfiniteᵒᵖ).unop) :=
      isEmpty_of_lightProfinite_isInitial _ terminalIsTerminal.unop
    letI : Unique (F.obj (⊤_ LightProfiniteᵒᵖ)) := by
      change Unique (BoundedRealSeqSection ((⊤_ LightProfiniteᵒᵖ).unop))
      infer_instance
    letI : PreservesLimit (Functor.empty (LightProfiniteᵒᵖ)) F :=
      preservesTerminal_of_iso F (Equiv.toIso (Equiv.ofUnique (F.obj (⊤_ LightProfiniteᵒᵖ)) PUnit) ≪≫
        (Types.terminalIso : (⊤_ Type) ≅ PUnit).symm)
    exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := F)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal F

/-- The light condensed abelian group of uniformly bounded real sequences. -/
noncomputable def boundedRealSequences : LightCondAb :=
  LightCondensed.ofSheafForgetLightProfinite boundedRealSeqPresheaf
    boundedRealSeqPresheaf_equalizerCondition_underlying

/-- Sections of `boundedRealSequences` are uniformly bounded sequences of continuous real-valued
functions, in subtype form. -/
noncomputable def boundedRealSequencesSectionsEquiv (S : LightProfinite) :
    boundedRealSequences.obj.obj ⟨S⟩ ≃ₗ[ℤ]
      { x : ℕ → C(S, ℝ) // ∃ N : ℕ, ∀ s n, ‖x n s‖ ≤ (N : ℝ) } :=
  (LinearEquiv.refl ℤ (BoundedRealSeqSection S)).trans
    (BoundedRealSeqSection.subtypeLinearEquiv S)

@[simp]
lemma boundedRealSequencesSectionsEquiv_apply_coe (S : LightProfinite)
    (x : boundedRealSequences.obj.obj ⟨S⟩) :
    ((boundedRealSequencesSectionsEquiv S x).1 : ℕ → C(S, ℝ)) =
      (show BoundedRealSeqSection S from x).val :=
  rfl

@[simp]
lemma boundedRealSequencesSectionsEquiv_map {S T : LightProfinite} (f : T ⟶ S)
    (x : boundedRealSequences.obj.obj ⟨S⟩) :
    (boundedRealSequencesSectionsEquiv T (boundedRealSequences.obj.map f.op x)).1 =
      fun n : ℕ => ((boundedRealSequencesSectionsEquiv S x).1 n).comp f.hom.hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coordinatewise inclusion of bounded real sequences into all real sequences. -/
noncomputable def boundedRealToProductReal : boundedRealSequences ⟶ productRealSequences where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => (productRealSequencesSectionsEquiv S.unop).symm
        (show BoundedRealSeqSection S.unop from x).val
      map_add' := by
        intro x y
        apply (productRealSequencesSectionsEquiv S.unop).injective
        rw [LinearEquiv.apply_symm_apply]
        rw [(productRealSequencesSectionsEquiv S.unop).map_add]
        ext n s
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        change (x + y).val n s = x.val n s + y.val n s
        rfl
      map_smul' := by
        intro a x
        apply (productRealSequencesSectionsEquiv S.unop).injective
        rw [LinearEquiv.apply_symm_apply]
        rw [(productRealSequencesSectionsEquiv S.unop).map_smul]
        rw [LinearEquiv.apply_symm_apply]
        change (a • x).val = a • x.val
        rfl }
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext x
      apply (productRealSequencesSectionsEquiv T.unop).injective
      dsimp
      ext n s
      rw [LinearEquiv.apply_symm_apply]
      change ((boundedRealSeqPresheaf.map φ (show BoundedRealSeqSection S.unop from x)).val n) s =
        (productRealSequencesSectionsEquiv T.unop
          (productRealSequences.obj.map φ
            ((productRealSequencesSectionsEquiv S.unop).symm
              (show BoundedRealSeqSection S.unop from x).val)) n) s
      rw [show φ = φ.unop.op by rfl]
      rw [productRealSequencesSectionsEquiv_map]
      rw [LinearEquiv.apply_symm_apply]
      rfl }

@[simp]
lemma boundedRealToProductReal_apply_coord (S : LightProfinite)
    (x : boundedRealSequences.obj.obj ⟨S⟩) (n : ℕ) :
    productRealSequencesSectionsEquiv S ((boundedRealToProductReal.hom.app ⟨S⟩) x) n =
      (boundedRealSequencesSectionsEquiv S x).1 n := by
  dsimp [boundedRealToProductReal, boundedRealSequencesSectionsEquiv]
  exact congrFun (LinearEquiv.apply_symm_apply (productRealSequencesSectionsEquiv S)
    (show BoundedRealSeqSection S from x).val) n

end ProjectiveGeneratorProof
end Solid
end LightCondensed
