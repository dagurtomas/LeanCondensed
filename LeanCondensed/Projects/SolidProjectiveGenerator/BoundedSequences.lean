module

public import LeanCondensed.Projects.SolidProjectiveGenerator.PBasics
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- Uniformly bounded sequences of locally constant integer-valued functions on a light profinite
space.  The bound is uniform both in the source point and in the sequence coordinate. -/
structure BoundedIntSeqSection (S : LightProfinite) where
  val : ℕ → LocallyConstant S ℤ
  isBounded : ∃ N : ℕ, ∀ s : S, ∀ n : ℕ, Int.natAbs (val n s) ≤ N

namespace BoundedIntSeqSection

@[ext]
lemma ext {S : LightProfinite} {x y : BoundedIntSeqSection S}
    (h : ∀ n : ℕ, x.val n = y.val n) : x = y := by
  cases x
  cases y
  simp only at h
  congr
  exact funext h

lemma ext_apply {S : LightProfinite} {x y : BoundedIntSeqSection S}
    (h : ∀ n : ℕ, ∀ s : S, x.val n s = y.val n s) : x = y := by
  apply ext
  intro n
  exact LocallyConstant.ext (h n)

lemma val_ext_iff {S : LightProfinite} {x y : BoundedIntSeqSection S} :
    x = y ↔ ∀ n : ℕ, x.val n = y.val n := by
  constructor
  · intro h n
    rw [h]
  · exact ext

instance (S : LightProfinite) : Zero (BoundedIntSeqSection S) where
  zero := {
    val := 0
    isBounded := by
      refine ⟨0, ?_⟩
      intro s n
      simp }

instance (S : LightProfinite) : Add (BoundedIntSeqSection S) where
  add x y := {
    val := fun n => x.val n + y.val n
    isBounded := by
      obtain ⟨Nx, hx⟩ := x.isBounded
      obtain ⟨Ny, hy⟩ := y.isBounded
      refine ⟨Nx + Ny, ?_⟩
      intro s n
      calc
        Int.natAbs ((x.val n + y.val n) s)
            = Int.natAbs (x.val n s + y.val n s) := rfl
        _ ≤ Int.natAbs (x.val n s) + Int.natAbs (y.val n s) :=
            Int.natAbs_add_le _ _
        _ ≤ Nx + Ny := Nat.add_le_add (hx s n) (hy s n) }

instance (S : LightProfinite) : Neg (BoundedIntSeqSection S) where
  neg x := {
    val := fun n => -x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨N, ?_⟩
      intro s n
      simpa [Int.natAbs_neg] using hN s n }

instance (S : LightProfinite) : Sub (BoundedIntSeqSection S) where
  sub x y := {
    val := fun n => x.val n - y.val n
    isBounded := by
      obtain ⟨Nx, hx⟩ := x.isBounded
      obtain ⟨Ny, hy⟩ := y.isBounded
      refine ⟨Nx + Ny, ?_⟩
      intro s n
      calc
        Int.natAbs ((x.val n - y.val n) s)
            = Int.natAbs (x.val n s - y.val n s) := rfl
        _ ≤ Int.natAbs (x.val n s) + Int.natAbs (y.val n s) :=
            Int.natAbs_sub_le _ _
        _ ≤ Nx + Ny := Nat.add_le_add (hx s n) (hy s n) }

instance (S : LightProfinite) : SMul ℕ (BoundedIntSeqSection S) where
  smul m x := {
    val := fun n => m • x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨m * N, ?_⟩
      intro s n
      calc
        Int.natAbs ((m • x.val n) s)
            = Int.natAbs (m • x.val n s) := rfl
        _ = Int.natAbs ((m : ℤ) * x.val n s) := by rw [nsmul_eq_mul]
        _ = m * Int.natAbs (x.val n s) := by rw [Int.natAbs_mul, Int.natAbs_natCast]
        _ ≤ m * N := Nat.mul_le_mul_left m (hN s n) }

instance (S : LightProfinite) : SMul ℤ (BoundedIntSeqSection S) where
  smul a x := {
    val := fun n => a • x.val n
    isBounded := by
      obtain ⟨N, hN⟩ := x.isBounded
      refine ⟨Int.natAbs a * N, ?_⟩
      intro s n
      calc
        Int.natAbs ((a • x.val n) s)
            = Int.natAbs (a • x.val n s) := rfl
        _ = Int.natAbs (a * x.val n s) := by simp
        _ = Int.natAbs a * Int.natAbs (x.val n s) := Int.natAbs_mul _ _
        _ ≤ Int.natAbs a * N := Nat.mul_le_mul_left (Int.natAbs a) (hN s n) }

instance (S : LightProfinite) : AddCommGroup (BoundedIntSeqSection S) :=
  Function.Injective.addCommGroup (fun x : BoundedIntSeqSection S => x.val)
    (fun _ _ h => ext (fun n => congrFun h n)) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance (S : LightProfinite) : Module ℤ (BoundedIntSeqSection S) :=
  AddCommGroup.toIntModule (BoundedIntSeqSection S)

@[simp]
lemma val_zero (S : LightProfinite) (n : ℕ) :
    (0 : BoundedIntSeqSection S).val n = 0 :=
  rfl

@[simp]
lemma val_add {S : LightProfinite} (x y : BoundedIntSeqSection S) (n : ℕ) :
    (x + y).val n = x.val n + y.val n :=
  rfl

@[simp]
lemma val_neg {S : LightProfinite} (x : BoundedIntSeqSection S) (n : ℕ) :
    (-x).val n = -x.val n :=
  rfl

@[simp]
lemma val_sub {S : LightProfinite} (x y : BoundedIntSeqSection S) (n : ℕ) :
    (x - y).val n = x.val n - y.val n :=
  rfl

@[simp]
lemma val_nsmul {S : LightProfinite} (m : ℕ) (x : BoundedIntSeqSection S) (n : ℕ) :
    (m • x).val n = m • x.val n :=
  rfl

@[simp]
lemma val_zsmul {S : LightProfinite} (a : ℤ) (x : BoundedIntSeqSection S) (n : ℕ) :
    (a • x).val n = a • x.val n :=
  rfl

end BoundedIntSeqSection

/-- Restrict a bounded integer sequence section along a map of light profinite spaces. -/
def boundedIntSeqSectionComap {S T : LightProfinite} (f : T ⟶ S)
    (x : BoundedIntSeqSection S) : BoundedIntSeqSection T where
  val n := (x.val n).comap f.hom.hom
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    exact ⟨N, fun t n => hN (f t) n⟩

@[simp]
lemma boundedIntSeqSectionComap_val {S T : LightProfinite} (f : T ⟶ S)
    (x : BoundedIntSeqSection S) (n : ℕ) :
    (boundedIntSeqSectionComap f x).val n = (x.val n).comap f.hom.hom :=
  rfl

/-- The presheaf of uniformly bounded integer sequences of locally constant functions. -/
noncomputable def boundedIntSeqPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ where
  obj S := ModuleCat.of ℤ (BoundedIntSeqSection S.unop)
  map {S T} f := ModuleCat.ofHom {
    toFun := boundedIntSeqSectionComap f.unop
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
lemma boundedIntSeqPresheaf_map_val {S T : LightProfinite} (f : T ⟶ S)
    (x : boundedIntSeqPresheaf.obj ⟨S⟩) (n : ℕ) :
    ((boundedIntSeqPresheaf.map f.op) x).val n = (x.val n).comap f.hom.hom :=
  rfl


def lightProfinitePEmptyIsInitial : IsInitial (LightProfinite.of PEmpty) := by
  refine IsInitial.ofUniqueHom (fun X => ConcreteCategory.ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩) ?_
  intro X f
  ext x
  exact PEmpty.elim x

lemma isEmpty_of_lightProfinite_isInitial (S : LightProfinite) (hS : IsInitial S) :
    IsEmpty S := by
  let e : S ≅ LightProfinite.of PEmpty := hS.uniqueUpToIso lightProfinitePEmptyIsInitial
  exact ⟨fun x => PEmpty.elim (e.hom x)⟩

instance uniqueSectionOfIsEmpty (S : LightProfinite) [IsEmpty S] :
    Unique (BoundedIntSeqSection S) where
  default := 0
  uniq x := by
    apply BoundedIntSeqSection.ext_apply
    intro n s
    exact isEmptyElim s



noncomputable def descendLocallyConstantInt {X B : LightProfinite} (π : X ⟶ B)
    [EffectiveEpi π] (c : PullbackCone π π) (hc : IsLimit c)
    (f : LocallyConstant X ℤ)
    (h : f.comap c.fst.hom.hom = f.comap c.snd.hom.hom) : LocallyConstant B ℤ := by
  let xZ : Zdisc.obj.obj ⟨X⟩ := (zdiscSectionsEquiv X).symm f
  have hxZ : ((forget ℤ).obj Zdisc).obj.map c.fst.op xZ =
      ((forget ℤ).obj Zdisc).obj.map c.snd.op xZ := by
    change Zdisc.obj.map c.fst.op xZ = Zdisc.obj.map c.snd.op xZ
    apply (zdiscSectionsEquiv c.pt).injective
    rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map]
    simp [xZ, h]
  let target : {x : ((forget ℤ).obj Zdisc).obj.obj ⟨X⟩ |
      ((forget ℤ).obj Zdisc).obj.map c.fst.op x =
        ((forget ℤ).obj Zdisc).obj.map c.snd.op x} := ⟨xZ, hxZ⟩
  have hbij := (LightCondensed.equalizerCondition ((forget ℤ).obj Zdisc)).bijective_mapToEqualizer_pullback' c hc
  let y := Classical.choose (hbij.2 target)
  exact zdiscSectionsEquiv B y

lemma descendLocallyConstantInt_spec {X B : LightProfinite} (π : X ⟶ B)
    [EffectiveEpi π] (c : PullbackCone π π) (hc : IsLimit c)
    (f : LocallyConstant X ℤ)
    (h : f.comap c.fst.hom.hom = f.comap c.snd.hom.hom) :
    (descendLocallyConstantInt π c hc f h).comap π.hom.hom = f := by
  dsimp [descendLocallyConstantInt]
  let xZ : Zdisc.obj.obj ⟨X⟩ := (zdiscSectionsEquiv X).symm f
  have hxZ : ((forget ℤ).obj Zdisc).obj.map c.fst.op xZ =
      ((forget ℤ).obj Zdisc).obj.map c.snd.op xZ := by
    change Zdisc.obj.map c.fst.op xZ = Zdisc.obj.map c.snd.op xZ
    apply (zdiscSectionsEquiv c.pt).injective
    rw [zdiscSectionsEquiv_map, zdiscSectionsEquiv_map]
    simp [xZ, h]
  let target : {x : ((forget ℤ).obj Zdisc).obj.obj ⟨X⟩ |
      ((forget ℤ).obj Zdisc).obj.map c.fst.op x =
        ((forget ℤ).obj Zdisc).obj.map c.snd.op x} := ⟨xZ, hxZ⟩
  have hbij := (LightCondensed.equalizerCondition ((forget ℤ).obj Zdisc)).bijective_mapToEqualizer_pullback' c hc
  let y := Classical.choose (hbij.2 target)
  have hy := Classical.choose_spec (hbij.2 target)
  have hy1 : ((forget ℤ).obj Zdisc).obj.map π.op y = xZ := by
    have hval := congrArg Subtype.val hy
    change (((forget ℤ).obj Zdisc).obj.map π.op y) = xZ at hval
    exact hval
  change LocallyConstant.comap π.hom.hom ((zdiscSectionsEquiv B) y) = f
  rw [← zdiscSectionsEquiv_map π y]
  change zdiscSectionsEquiv X (((forget ℤ).obj Zdisc).obj.map π.op y) = f
  rw [hy1]
  simp [xZ]

lemma boundedIntSeqPresheaf_equalizerCondition_underlying :
    regularTopology.EqualizerCondition
      (boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := by
  apply regularTopology.EqualizerCondition.mk'
  intro X B π hπ c hc
  constructor
  · intro a b hab
    have hmap : boundedIntSeqPresheaf.map π.op a = boundedIntSeqPresheaf.map π.op b := by
      have hval := congrArg Subtype.val hab
      change (boundedIntSeqPresheaf.map π.op a) = boundedIntSeqPresheaf.map π.op b at hval
      exact hval
    apply BoundedIntSeqSection.ext_apply
    intro n s
    haveI : Epi π := inferInstance
    have hsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp inferInstance
    obtain ⟨x, hx⟩ := hsurj s
    have hcoord := congrArg (fun z : BoundedIntSeqSection X => z.val n) hmap
    have hpoint := congrArg (fun f : LocallyConstant X ℤ => f x) hcoord
    change a.val n (π x) = b.val n (π x) at hpoint
    simpa [hx] using hpoint
  · intro target
    let yX : BoundedIntSeqSection X := target.1
    have compat : boundedIntSeqPresheaf.map c.fst.op yX =
        boundedIntSeqPresheaf.map c.snd.op yX := target.2
    let yB : BoundedIntSeqSection B := {
      val := fun n =>
        descendLocallyConstantInt π c hc (yX.val n) (by
          have hcoord := congrArg (fun z : BoundedIntSeqSection c.pt => z.val n) compat
          exact hcoord)
      isBounded := by
        obtain ⟨N, hN⟩ := yX.isBounded
        refine ⟨N, ?_⟩
        intro b n
        haveI : Epi π := inferInstance
        have hsurj : Function.Surjective π := (LightProfinite.epi_iff_surjective π).mp inferInstance
        obtain ⟨x, hx⟩ := hsurj b
        have hspec := descendLocallyConstantInt_spec π c hc (yX.val n) (by
          have hcoord := congrArg (fun z : BoundedIntSeqSection c.pt => z.val n) compat
          exact hcoord)
        have hpoint := congrArg (fun f : LocallyConstant X ℤ => f x) hspec
        change (descendLocallyConstantInt π c hc (yX.val n) _ (π x)) = yX.val n x at hpoint
        rw [hx] at hpoint
        rw [hpoint]
        exact hN x n }
    refine ⟨yB, ?_⟩
    apply Subtype.ext
    apply BoundedIntSeqSection.ext
    intro n
    exact descendLocallyConstantInt_spec π c hc (yX.val n) (by
      have hcoord := congrArg (fun z : BoundedIntSeqSection c.pt => z.val n) compat
      exact hcoord)


lemma binaryProduct_jointly_surjective {S T : LightProfiniteᵒᵖ} (p : (S ⨯ T).unop) :
    (∃ s : S.unop, (prod.fst : S ⨯ T ⟶ S).unop s = p) ∨
      (∃ t : T.unop, (prod.snd : S ⨯ T ⟶ T).unop t = p) := by
  let hc := isColimitOfPreserves (LightProfinite.toTopCat ⋙ CategoryTheory.forget TopCat)
    (BinaryFan.IsLimit.unop (prodIsProd S T))
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc p
  rcases j with ⟨j⟩
  cases j
  · left
    exact ⟨y, hy⟩
  · right
    exact ⟨y, hy⟩

noncomputable def glueZdiscBinary {S T : LightProfiniteᵒᵖ}
    (xS : Zdisc.obj.obj S) (xT : Zdisc.obj.obj T) : Zdisc.obj.obj (S ⨯ T) := by
  let F := ((forget ℤ).obj Zdisc).obj
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv (xS, xT)
  exact inv (prodComparison F S T) pair

lemma glueZdiscBinary_fst {S T : LightProfiniteᵒᵖ}
    (xS : Zdisc.obj.obj S) (xT : Zdisc.obj.obj T) :
    Zdisc.obj.map (prod.fst : S ⨯ T ⟶ S).unop.op (glueZdiscBinary xS xT) = xS := by
  let F := ((forget ℤ).obj Zdisc).obj
  dsimp [glueZdiscBinary]
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv (xS, xT)
  have h := congrArg (fun f : F.obj S ⨯ F.obj T ⟶ F.obj S => f pair)
    (inv_prodComparison_map_fst (F := F) (A := S) (B := T))
  change F.map (prod.fst : S ⨯ T ⟶ S)
      (inv (prodComparison F S T)
        ((Types.binaryProductIso (F.obj S) (F.obj T)).inv (xS, xT))) = xS
  simpa [pair] using h

lemma glueZdiscBinary_snd {S T : LightProfiniteᵒᵖ}
    (xS : Zdisc.obj.obj S) (xT : Zdisc.obj.obj T) :
    Zdisc.obj.map (prod.snd : S ⨯ T ⟶ T).unop.op (glueZdiscBinary xS xT) = xT := by
  let F := ((forget ℤ).obj Zdisc).obj
  dsimp [glueZdiscBinary]
  let pair : F.obj S ⨯ F.obj T :=
    (Types.binaryProductIso (F.obj S) (F.obj T)).inv (xS, xT)
  have h := congrArg (fun f : F.obj S ⨯ F.obj T ⟶ F.obj T => f pair)
    (inv_prodComparison_map_snd (F := F) (A := S) (B := T))
  change F.map (prod.snd : S ⨯ T ⟶ T)
      (inv (prodComparison F S T)
        ((Types.binaryProductIso (F.obj S) (F.obj T)).inv (xS, xT))) = xT
  simpa [pair] using h

noncomputable def glueLocallyConstantBinary {S T : LightProfiniteᵒᵖ}
    (xS : LocallyConstant S.unop ℤ) (xT : LocallyConstant T.unop ℤ) :
    LocallyConstant (S ⨯ T).unop ℤ :=
  zdiscSectionsEquiv (S ⨯ T).unop
    (glueZdiscBinary ((zdiscSectionsEquiv S.unop).symm xS) ((zdiscSectionsEquiv T.unop).symm xT))

lemma glueLocallyConstantBinary_fst {S T : LightProfiniteᵒᵖ}
    (xS : LocallyConstant S.unop ℤ) (xT : LocallyConstant T.unop ℤ) :
    (glueLocallyConstantBinary xS xT).comap (prod.fst : S ⨯ T ⟶ S).unop.hom.hom = xS := by
  dsimp [glueLocallyConstantBinary]
  rw [← zdiscSectionsEquiv_map]
  rw [glueZdiscBinary_fst]
  simp

lemma glueLocallyConstantBinary_snd {S T : LightProfiniteᵒᵖ}
    (xS : LocallyConstant S.unop ℤ) (xT : LocallyConstant T.unop ℤ) :
    (glueLocallyConstantBinary xS xT).comap (prod.snd : S ⨯ T ⟶ T).unop.hom.hom = xT := by
  dsimp [glueLocallyConstantBinary]
  rw [← zdiscSectionsEquiv_map]
  rw [glueZdiscBinary_snd]
  simp


noncomputable def glueBoundedBinary {S T : LightProfiniteᵒᵖ}
    (xS : BoundedIntSeqSection S.unop) (xT : BoundedIntSeqSection T.unop) :
    BoundedIntSeqSection (S ⨯ T).unop where
  val n := glueLocallyConstantBinary (xS.val n) (xT.val n)
  isBounded := by
    obtain ⟨NS, hS⟩ := xS.isBounded
    obtain ⟨NT, hT⟩ := xT.isBounded
    refine ⟨max NS NT, ?_⟩
    intro p n
    rcases binaryProduct_jointly_surjective (S := S) (T := T) p with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · have hfst := glueLocallyConstantBinary_fst (S := S) (T := T) (xS.val n) (xT.val n)
      have hp := congrArg (fun f : LocallyConstant S.unop ℤ => f s) hfst
      change (glueLocallyConstantBinary (xS.val n) (xT.val n)) ((prod.fst : S ⨯ T ⟶ S).unop s) =
        xS.val n s at hp
      rw [hp]
      exact le_trans (hS s n) (Nat.le_max_left NS NT)
    · have hsnd := glueLocallyConstantBinary_snd (S := S) (T := T) (xS.val n) (xT.val n)
      have hp := congrArg (fun f : LocallyConstant T.unop ℤ => f t) hsnd
      change (glueLocallyConstantBinary (xS.val n) (xT.val n)) ((prod.snd : S ⨯ T ⟶ T).unop t) =
        xT.val n t at hp
      rw [hp]
      exact le_trans (hT t n) (Nat.le_max_right NS NT)

lemma glueBoundedBinary_fst {S T : LightProfiniteᵒᵖ}
    (xS : BoundedIntSeqSection S.unop) (xT : BoundedIntSeqSection T.unop) :
    boundedIntSeqPresheaf.map (prod.fst : S ⨯ T ⟶ S) (glueBoundedBinary xS xT) = xS := by
  apply BoundedIntSeqSection.ext
  intro n
  exact glueLocallyConstantBinary_fst (S := S) (T := T) (xS.val n) (xT.val n)

lemma glueBoundedBinary_snd {S T : LightProfiniteᵒᵖ}
    (xS : BoundedIntSeqSection S.unop) (xT : BoundedIntSeqSection T.unop) :
    boundedIntSeqPresheaf.map (prod.snd : S ⨯ T ⟶ T) (glueBoundedBinary xS xT) = xT := by
  apply BoundedIntSeqSection.ext
  intro n
  exact glueLocallyConstantBinary_snd (S := S) (T := T) (xS.val n) (xT.val n)

instance boundedIntSeqPresheaf_prodComparison_isIso (S T : LightProfiniteᵒᵖ) :
    IsIso (prodComparison (boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) S T) := by
  apply (isIso_iff_bijective (prodComparison
    (boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) S T)).mpr
  constructor
  · intro a b hab
    apply BoundedIntSeqSection.ext_apply
    intro n p
    rcases binaryProduct_jointly_surjective (S := S) (T := T) p with ⟨s, hs⟩ | ⟨t, ht⟩
    · let F := boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
      have hfst : F.map (prod.fst : S ⨯ T ⟶ S) a = F.map (prod.fst : S ⨯ T ⟶ S) b := by
        have h := congrArg (fun q => (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) q) hab
        have ha := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f a)
          (prodComparison_fst F S T)
        have hb := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f b)
          (prodComparison_fst F S T)
        exact ha.symm.trans (h.trans hb)
      have hcoord := congrArg (fun z : BoundedIntSeqSection S.unop => z.val n) hfst
      have hp := congrArg (fun f : LocallyConstant S.unop ℤ => f s) hcoord
      change a.val n ((prod.fst : S ⨯ T ⟶ S).unop s) = b.val n ((prod.fst : S ⨯ T ⟶ S).unop s) at hp
      simpa [hs] using hp
    · let F := boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
      have hsnd : F.map (prod.snd : S ⨯ T ⟶ T) a = F.map (prod.snd : S ⨯ T ⟶ T) b := by
        have h := congrArg (fun q => (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) q) hab
        have ha := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f a)
          (prodComparison_snd F S T)
        have hb := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f b)
          (prodComparison_snd F S T)
        exact ha.symm.trans (h.trans hb)
      have hcoord := congrArg (fun z : BoundedIntSeqSection T.unop => z.val n) hsnd
      have hp := congrArg (fun f : LocallyConstant T.unop ℤ => f t) hcoord
      change a.val n ((prod.snd : S ⨯ T ⟶ T).unop t) = b.val n ((prod.snd : S ⨯ T ⟶ T).unop t) at hp
      simpa [ht] using hp
  · intro y
    let F := boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
    let xS : BoundedIntSeqSection S.unop := (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) y
    let xT : BoundedIntSeqSection T.unop := (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) y
    let g : F.obj (S ⨯ T) := glueBoundedBinary xS xT
    refine ⟨g, ?_⟩
    apply (Types.binaryProductIso (F.obj S) (F.obj T)).toEquiv.injective
    apply Prod.ext
    · change ((Types.binaryProductIso (F.obj S) (F.obj T)).hom
          (prodComparison F S T g)).1 = ((Types.binaryProductIso (F.obj S) (F.obj T)).hom y).1
      rw [Types.binaryProductIso_hom_comp_fst_apply,
        Types.binaryProductIso_hom_comp_fst_apply]
      have hcomp := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj S => f g)
        (prodComparison_fst F S T)
      change (prodComparison F S T ≫ prod.fst) g = (prod.fst : F.obj S ⨯ F.obj T ⟶ F.obj S) y
      rw [hcomp]
      change boundedIntSeqPresheaf.map (prod.fst : S ⨯ T ⟶ S)
        (glueBoundedBinary xS xT) = xS
      exact glueBoundedBinary_fst xS xT
    · change ((Types.binaryProductIso (F.obj S) (F.obj T)).hom
          (prodComparison F S T g)).2 = ((Types.binaryProductIso (F.obj S) (F.obj T)).hom y).2
      rw [Types.binaryProductIso_hom_comp_snd_apply,
        Types.binaryProductIso_hom_comp_snd_apply]
      have hcomp := congrArg (fun f : F.obj (S ⨯ T) ⟶ F.obj T => f g)
        (prodComparison_snd F S T)
      change (prodComparison F S T ≫ prod.snd) g = (prod.snd : F.obj S ⨯ F.obj T ⟶ F.obj T) y
      rw [hcomp]
      change boundedIntSeqPresheaf.map (prod.snd : S ⨯ T ⟶ T)
        (glueBoundedBinary xS xT) = xT
      exact glueBoundedBinary_snd xS xT



instance boundedIntSeqPresheaf_preservesFiniteProducts_underlying :
    PreservesFiniteProducts (boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) := by
  let F := boundedIntSeqPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryProducts_of_isIso_prodComparison F
  haveI : PreservesLimitsOfShape (Discrete.{0} PEmpty) F := by
    haveI : IsEmpty ((⊤_ LightProfiniteᵒᵖ).unop) :=
      isEmpty_of_lightProfinite_isInitial _ terminalIsTerminal.unop
    letI : Unique (F.obj (⊤_ LightProfiniteᵒᵖ)) := by
      change Unique (BoundedIntSeqSection ((⊤_ LightProfiniteᵒᵖ).unop))
      infer_instance
    letI : PreservesLimit (Functor.empty (LightProfiniteᵒᵖ)) F :=
      preservesTerminal_of_iso F (Equiv.toIso (Equiv.ofUnique (F.obj (⊤_ LightProfiniteᵒᵖ)) PUnit) ≪≫
        (Types.terminalIso : (⊤_ Type) ≅ PUnit).symm)
    exact preservesLimitsOfShape_pempty_of_preservesTerminal (G := F)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal F

/-- The light condensed abelian group of uniformly bounded integer sequences. -/
noncomputable def boundedIntSequences : LightCondAb :=
  LightCondensed.ofSheafForgetLightProfinite boundedIntSeqPresheaf
    boundedIntSeqPresheaf_equalizerCondition_underlying

/-- Sections of `boundedIntSequences` are bounded integer sequence sections. -/
noncomputable def boundedIntSequencesSectionsEquiv (S : LightProfinite) :
    boundedIntSequences.obj.obj ⟨S⟩ ≃ₗ[ℤ] BoundedIntSeqSection S :=
  LinearEquiv.refl ℤ _

set_option backward.isDefEq.respectTransparency false in
/-- The coordinatewise inclusion of bounded integer sequences into all integer sequences. -/
noncomputable def boundedToProduct : boundedIntSequences ⟶ productIntLight where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => (productIntLocallyConstantSectionsEquiv S.unop).symm
        (show BoundedIntSeqSection S.unop from x).val
      map_add' := by
        intro x y
        apply (productIntLocallyConstantSectionsEquiv S.unop).injective
        rw [LinearEquiv.apply_symm_apply]
        rw [(productIntLocallyConstantSectionsEquiv S.unop).map_add]
        ext n s
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        change (x + y).val n s = x.val n s + y.val n s
        rfl
      map_smul' := by
        intro a x
        apply (productIntLocallyConstantSectionsEquiv S.unop).injective
        rw [LinearEquiv.apply_symm_apply]
        rw [(productIntLocallyConstantSectionsEquiv S.unop).map_smul]
        rw [LinearEquiv.apply_symm_apply]
        change (a • x).val = a • x.val
        rfl }
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext x
      apply (productIntLocallyConstantSectionsEquiv T.unop).injective
      dsimp
      ext n s
      rw [LinearEquiv.apply_symm_apply]
      change ((boundedIntSeqPresheaf.map φ (show BoundedIntSeqSection S.unop from x)).val n) s =
        (productIntLocallyConstantSectionsEquiv T.unop
          (productIntLight.obj.map φ
            ((productIntLocallyConstantSectionsEquiv S.unop).symm
              (show BoundedIntSeqSection S.unop from x).val)) n) s
      rw [show φ = φ.unop.op by rfl]
      rw [productIntLocallyConstantSectionsEquiv_map]
      rw [LinearEquiv.apply_symm_apply]
      rfl }

@[simp]
lemma boundedToProduct_apply_coord (S : LightProfinite)
    (x : boundedIntSequences.obj.obj ⟨S⟩) (n : ℕ) :
    productIntLocallyConstantSectionsEquiv S ((boundedToProduct.hom.app ⟨S⟩) x) n =
      (boundedIntSequencesSectionsEquiv S x).val n := by
  dsimp [boundedToProduct, boundedIntSequencesSectionsEquiv]
  exact congrFun (LinearEquiv.apply_symm_apply (productIntLocallyConstantSectionsEquiv S)
    (show BoundedIntSeqSection S from x).val) n

/-- In-place truncation of a bounded sequence section: coordinates before `n` are set to zero,
and all later coordinates keep their original positions. -/
def boundedTailProjectionSection (n : ℕ) {S : LightProfinite}
    (x : BoundedIntSeqSection S) : BoundedIntSeqSection S where
  val k := if n ≤ k then x.val k else 0
  isBounded := by
    obtain ⟨N, hN⟩ := x.isBounded
    refine ⟨N, ?_⟩
    intro s k
    by_cases h : n ≤ k
    · simpa [h] using hN s k
    · simp [h]

@[simp]
lemma boundedTailProjectionSection_val (n : ℕ) {S : LightProfinite}
    (x : BoundedIntSeqSection S) (k : ℕ) :
    (boundedTailProjectionSection n x).val k = if n ≤ k then x.val k else 0 :=
  rfl

/-- The in-place bounded-tail projection.  The finite stage `n` keeps the coordinates `k ≥ n`
and zeroes the first `n` coordinates. -/
noncomputable def boundedTailProjection (n : ℕ) :
    boundedIntSequences ⟶ boundedIntSequences where
  hom := {
    app S := ModuleCat.ofHom {
      toFun := fun x => boundedTailProjectionSection n (show BoundedIntSeqSection S.unop from x)
      map_add' := by
        intro x y
        apply BoundedIntSeqSection.ext
        intro k
        by_cases h : n ≤ k <;> ext s <;> simp [boundedTailProjectionSection, h]
      map_smul' := by
        intro a x
        apply BoundedIntSeqSection.ext
        intro k
        by_cases h : n ≤ k <;> ext s <;> simp [boundedTailProjectionSection, h] }
    naturality := by
      intro S T φ
      rw [show φ = φ.unop.op by rfl]
      ext x
      change boundedTailProjectionSection n
          (boundedIntSeqSectionComap φ.unop (show BoundedIntSeqSection S.unop from x)) =
        boundedIntSeqSectionComap φ.unop
          (boundedTailProjectionSection n (show BoundedIntSeqSection S.unop from x))
      apply BoundedIntSeqSection.ext_apply
      intro k s
      by_cases h : n ≤ k <;> simp [boundedTailProjectionSection, boundedIntSeqSectionComap, h] }

@[simp]
lemma boundedTailProjection_apply_coord (n : ℕ) (S : LightProfinite)
    (x : boundedIntSequences.obj.obj ⟨S⟩) (k : ℕ) :
    (boundedIntSequencesSectionsEquiv S ((boundedTailProjection n).hom.app ⟨S⟩ x)).val k =
      if n ≤ k then (boundedIntSequencesSectionsEquiv S x).val k else 0 := by
  rfl

@[simp]
lemma boundedTailProjection_zero :
    boundedTailProjection 0 = 𝟙 boundedIntSequences := by
  ext S x
  change boundedTailProjectionSection 0 (show BoundedIntSeqSection S.unop from x) = x
  apply BoundedIntSeqSection.ext
  intro k
  simp [boundedTailProjectionSection]

@[simp]
lemma boundedTailProjection_succ_diff_apply_coord (n : ℕ) (S : LightProfinite)
    (x : boundedIntSequences.obj.obj ⟨S⟩) (k : ℕ) :
    (boundedIntSequencesSectionsEquiv S
      (((boundedTailProjection n - boundedTailProjection (n + 1)).hom.app ⟨S⟩) x)).val k =
      if k = n then (boundedIntSequencesSectionsEquiv S x).val n else 0 := by
  change ((boundedIntSequencesSectionsEquiv S ((boundedTailProjection n).hom.app ⟨S⟩ x) -
        boundedIntSequencesSectionsEquiv S ((boundedTailProjection (n + 1)).hom.app ⟨S⟩ x)).val k) =
      if k = n then (boundedIntSequencesSectionsEquiv S x).val n else 0
  rw [BoundedIntSeqSection.val_sub]
  rw [boundedTailProjection_apply_coord, boundedTailProjection_apply_coord]
  by_cases hkn : k = n
  · subst k
    ext s
    simp
  · rw [if_neg hkn]
    by_cases hnk : n ≤ k
    · have hn1k : n + 1 ≤ k := by omega
      ext s
      simp [hnk, hn1k]
    · have hn1k : ¬ n + 1 ≤ k := by omega
      ext s
      simp [hnk, hn1k]

/-- For every fixed coordinate, the in-place bounded-tail projections are eventually zero. -/
lemma boundedTailProjection_eventually_coord_zero (S : LightProfinite)
    (x : boundedIntSequences.obj.obj ⟨S⟩) (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (boundedIntSequencesSectionsEquiv S ((boundedTailProjection n).hom.app ⟨S⟩ x)).val k = 0 := by
  refine Filter.eventually_atTop.2 ⟨k + 1, ?_⟩
  intro n hn
  rw [boundedTailProjection_apply_coord]
  simp [show ¬ n ≤ k by omega]


end ProjectiveGeneratorProof
end Solid
end LightCondensed
