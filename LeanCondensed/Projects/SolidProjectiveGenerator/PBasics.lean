/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import LeanCondensed.Projects.LightSolid
public import LeanCondensed.Projects.FreeCondensed
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.Condensed.Discrete.Colimit
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The projective generator of solid abelian groups

This file isolates the categorical shell for the proof that the countable product of copies of
`ℤ` is a projective generator of `Solid`.  The hard analytic/derived inputs from the proof are kept
as explicit named obligations:

* `solidPIsoProduct`, identifying `solidification.obj (P ℤ)` with the countable product of `ℤ`;
* `solidifiedFreeRetractSolidPInfinite`, the infinite-test-object shift-retract calculation.

The remaining declarations are formal category-theory consequences of these named inputs, together
with the ordinary projectivity of `P ℤ`, the separation statement for solidified free
representables, and the finite-coproduct reduction proved below.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace CategoryTheory

/-- Separators are invariant under isomorphism. -/
lemma isSeparator_of_iso {C : Type*} [Category C]
    {G H : C} (e : G ≅ H) (hG : IsSeparator G) :
    IsSeparator H := by
  rw [isSeparator_def] at hG ⊢
  exact fun _ _ f g hH ↦ hG f g fun k ↦ by simpa using e.hom ≫= hH (e.inv ≫ k)

/-- If a jointly separating family consists of retracts of `G`, then `G` is a separator. -/
lemma isSeparator_of_retracts_of_hom_ext {C : Type*} [Category C] {I : Type*} (F : I → C) (G : C)
    (hjoint : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i (k : F i ⟶ X), k ≫ f = k ≫ g) → f = g)
    (r : ∀ i, Retract (F i) G) : IsSeparator G := by
  rw [isSeparator_def]
  exact fun _ _ f g hG ↦ hjoint f g fun i k ↦ by simpa using (r i).i ≫= hG ((r i).r ≫ k)

/-- If a functor preserves a binary coproduct and the target has zero morphisms, the image of the
first summand is a retract of the image of the coproduct. -/
noncomputable def functor_obj_retract_coprod
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms D]
    (F : C ⥤ D) (X Y : C) [HasBinaryCoproduct X Y] [HasBinaryCoproduct (F.obj X) (F.obj Y)]
    [PreservesColimit (pair X Y) F] : Retract (F.obj X) (F.obj (X ⨿ Y)) where
  i := F.map (coprod.inl : X ⟶ X ⨿ Y)
  r := inv (coprodComparison F X Y) ≫ coprod.desc (𝟙 (F.obj X)) 0
  retract := by rw [map_inl_inv_coprodComparison_assoc, coprod.inl_desc]

set_option backward.isDefEq.respectTransparency false in
/-- If the tensor unit is projective, internal projectivity implies ordinary projectivity.
This packages the standard adjunction argument: maps out of `P` are global sections of
`P ⟶[C] -`, and `P ⟶[C] -` preserves epimorphisms by internal projectivity. -/
lemma projective_of_internallyProjective_of_projective_unit
    {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
    (P : C) [Projective (𝟙_ C)] [InternallyProjective P] : Projective P where
  factors {E X} f e he := by
    obtain ⟨g', hg'⟩ := Projective.factors (MonoidalClosed.curry ((ρ_ P).hom ≫ f)) ((ihom P).map e)
    refine ⟨(ρ_ P).inv ≫ MonoidalClosed.uncurry g', ?_⟩
    simpa [MonoidalClosed.uncurry_natural_right] using (ρ_ P).inv ≫=
      (congrArg MonoidalClosed.uncurry hg')

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Abstract data for the shift-retract diagram used in the projective-generator proof. -/
structure ShiftRetractData (L : C ⥤ D) where
  xObj : C
  aObj : C
  bObj : C
  s : xObj ⟶ xObj
  toB : xObj ⟶ bObj
  toA : xObj ⟶ aObj
  g : aObj ⟶ bObj
  comm : s ≫ toB = toA ≫ g
  sect : bObj ⟶ xObj
  sect_fac : sect ≫ toB = 𝟙 bObj
  inverted : IsIso (L.map s)

namespace ShiftRetractData

/-- The formal retract extracted from a shift-retract square after applying a functor that inverts
its left vertical map. -/
noncomputable def retract {L : C ⥤ D}
    (d : ShiftRetractData L) : Retract (L.obj d.bObj) (L.obj d.aObj) := by
  letI := d.inverted
  refine {
    i := L.map d.sect ≫ inv (L.map d.s) ≫ L.map d.toA
    r := L.map d.g
    retract := ?_ }
  have hcomm : L.map d.s ≫ L.map d.toB = L.map d.toA ≫ L.map d.g := by
    simpa only [Functor.map_comp] using congrArg (fun f => L.map f) d.comm
  calc
    (L.map d.sect ≫ inv (L.map d.s) ≫ L.map d.toA) ≫ L.map d.g
        = L.map d.sect ≫ inv (L.map d.s) ≫ (L.map d.toA ≫ L.map d.g) := by
          simp [Category.assoc]
    _ = L.map d.sect ≫ inv (L.map d.s) ≫ (L.map d.s ≫ L.map d.toB) := by
          rw [← hcomm]
    _ = L.map d.sect ≫ L.map d.toB := by
          simp
    _ = L.map (d.sect ≫ d.toB) := by
          rw [Functor.map_comp]
    _ = 𝟙 (L.obj d.bObj) := by
          rw [d.sect_fac, Functor.map_id]

/-- If the complementary idempotent extracted from a shift-retract diagram is the identity, then
`L.map d.g` is an isomorphism. -/
lemma isIso_map_g {L : C ⥤ D}
    (d : ShiftRetractData L)
    (hidempotent : L.map d.g ≫ (d.retract).i = 𝟙 (L.obj d.aObj)) :
    IsIso (L.map d.g) := by
  letI := d.inverted
  exact ⟨(d.retract).i, hidempotent, d.retract.retract⟩

end ShiftRetractData

end CategoryTheory

namespace LightProfinite

/-- A surjection of light profinite spaces onto a finite target admits a section. -/
lemma exists_section_of_epi_to_finite {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] : ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y := by
  have hf : Function.Surjective f := (LightProfinite.epi_iff_surjective f).mp inferInstance
  let sFun : Y → X := fun y => (hf y).choose
  have hsFun : ∀ y, f (sFun y) = y := fun y => (hf y).choose_spec
  letI : DiscreteTopology Y := Finite.instDiscreteTopology
  let s : Y ⟶ X := ConcreteCategory.ofHom ⟨sFun, continuous_of_discreteTopology⟩
  refine ⟨s, ?_⟩
  ext y
  exact hsFun y

/-- A chosen section of a surjection of light profinite spaces onto a finite target. -/
noncomputable def sectionOfEpiToFinite {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] : Y ⟶ X :=
  (exists_section_of_epi_to_finite f).choose

@[simp]
lemma sectionOfEpiToFinite_comp {X Y : LightProfinite} [Finite Y]
    (f : X ⟶ Y) [Epi f] :
    sectionOfEpiToFinite f ≫ f = 𝟙 Y :=
  (exists_section_of_epi_to_finite f).choose_spec

/-- The finite stages in the standard inverse-limit presentation are finite. -/
instance finite_component (T : LightProfinite) (n : ℕ) : Finite (T.component n) :=
  inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj (T.fintypeDiagram.obj ⟨n⟩)))

/-- A chosen section of the projection from a light profinite set to a finite stage. -/
noncomputable def projSection (T : LightProfinite) (n : ℕ) : T.component n ⟶ T := by
  haveI : Epi (T.proj n) :=
    (LightProfinite.epi_iff_surjective _).mpr (T.proj_surjective n)
  exact sectionOfEpiToFinite (T.proj n)

@[simp]
lemma projSection_proj (T : LightProfinite) (n : ℕ) :
    projSection T n ≫ T.proj n = 𝟙 (T.component n) := by
  dsimp [projSection]
  haveI : Epi (T.proj n) :=
    (LightProfinite.epi_iff_surjective _).mpr (T.proj_surjective n)
  exact sectionOfEpiToFinite_comp (T.proj n)

/-- A section of the `n`th projection has the expected projection to every earlier finite stage. -/
lemma projSection_proj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    projSection T n ≫ T.proj k = T.transitionMapLE h := by
  rw [← T.proj_comp_transitionMapLE h]
  rw [← Category.assoc, projSection_proj]
  simp

/-- The finite-rank endomorphism of `T` obtained by projecting to the `n`th finite quotient and
returning along the chosen section. -/
noncomputable def finiteApproxRetraction (T : LightProfinite) (n : ℕ) : T ⟶ T :=
  T.proj n ≫ projSection T n

@[simp]
lemma finiteApproxRetraction_proj (T : LightProfinite) (n : ℕ) :
    finiteApproxRetraction T n ≫ T.proj n = T.proj n := by
  simp [finiteApproxRetraction, Category.assoc]

/-- The finite-rank retraction agrees with the identity on all finite stages up to `n`. -/
lemma finiteApproxRetraction_proj_le (T : LightProfinite) {k n : ℕ} (h : k ≤ n) :
    finiteApproxRetraction T n ≫ T.proj k = T.proj k := by
  calc
    finiteApproxRetraction T n ≫ T.proj k
        = T.proj n ≫ (projSection T n ≫ T.proj k) := by
          rw [finiteApproxRetraction, Category.assoc]
    _ = T.proj n ≫ T.transitionMapLE h := by
          rw [projSection_proj_le]
    _ = T.proj k := T.proj_comp_transitionMapLE h

/-- A locally constant function on a light profinite space factors through one of the finite stages
in the chosen sequential presentation. -/
lemma exists_locallyConstant_factor_proj (T : LightProfinite) {α : Type*}
    (f : LocallyConstant T α) :
    ∃ k : ℕ, ∃ g : LocallyConstant (T.component k) α,
      f = g.comap (T.proj k).hom.hom := by
  have hlim : IsLimit (lightToProfinite.mapCone T.asLimitCone) :=
    isLimitOfPreserves lightToProfinite T.asLimit
  obtain ⟨j, g, hg⟩ := Profinite.exists_locallyConstant
    (C := lightToProfinite.mapCone T.asLimitCone) hlim f
  exact ⟨j.unop, g, hg⟩

/-- In a light profinite space, a point outside a finite set has a clopen neighborhood disjoint from
that finite set. -/
lemma exists_clopen_avoiding_finset (T : LightProfinite)
    (s : Finset T) {t : T} (ht : t ∉ s) :
    ∃ U : Set T, IsClopen U ∧ t ∈ U ∧ ∀ u ∈ s, u ∉ U := by
  have hsclosed : IsClosed ((s : Set T)) := s.finite_toSet.isClosed
  have hopen : IsOpen ((s : Set T)ᶜ) := hsclosed.isOpen_compl
  have htmem : t ∈ ((s : Set T)ᶜ) := by simpa using ht
  obtain ⟨U, hU, htU, hUsub⟩ := compact_exists_isClopen_in_isOpen hopen htmem
  refine ⟨U, hU, htU, ?_⟩
  intro u hus huU
  exact hUsub huU hus

end LightProfinite

namespace LightCondensed
namespace Solid

/-- The solid abelian group `ℤ`. -/
noncomputable abbrev solidInteger : Solid :=
  ⟨(LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ), isSolid_int⟩

/-- The intended projective generator of solid abelian groups: a countable product of copies of
`ℤ`. -/
noncomputable abbrev solidProjectiveGenerator : Solid :=
  ∏ᶜ fun _ : ℕ => solidInteger

namespace ProjectiveGeneratorProof

/-- The discrete light condensed abelian group `ℤ`. -/
abbrev Zdisc : LightCondAb :=
  (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

-- Sections of the discrete light condensed abelian group `ℤ` are locally constant integer-valued
-- functions.
set_option backward.isDefEq.respectTransparency false in
noncomputable def zdiscSectionsEquiv (S : LightProfinite) :
    Zdisc.obj.obj ⟨S⟩ ≃ LocallyConstant S ℤ where
  toFun x := by
    let y := ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app
      (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩ x
    change LocallyConstant S ℤ at y
    exact y
  invFun y := by
    let x : ((LightCondMod.LocallyConstant.functor ℤ).obj (ModuleCat.of ℤ ℤ)).obj.obj ⟨S⟩ := y
    exact ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).hom.app
      (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩ x
  left_inv x := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)
    change (e.inv ≫ e.hom).hom.app ⟨S⟩ x = x
    rw [Iso.inv_hom_id]
    rfl
  right_inv y := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)
    change (e.hom ≫ e.inv).hom.app ⟨S⟩ y = y
    rw [Iso.hom_inv_id]
    rfl

/-- The locally constant-function description of `ℤ`-sections is natural in the test object. -/
lemma zdiscSectionsEquiv_map {S S' : LightProfinite} (φ : S' ⟶ S)
    (x : Zdisc.obj.obj ⟨S⟩) :
    zdiscSectionsEquiv S' (Zdisc.obj.map φ.op x) =
      (zdiscSectionsEquiv S x).comap φ.hom.hom := by
  dsimp [zdiscSectionsEquiv]
  exact LightCondMod.hom_naturality_apply ℤ
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)) φ.op x

@[simp]
lemma zdiscSectionsEquiv_zero (S : LightProfinite) :
    zdiscSectionsEquiv S (0 : Zdisc.obj.obj ⟨S⟩) = 0 := by
  dsimp [zdiscSectionsEquiv]
  simp
  rfl

/-- Sections of a discrete light condensed module are locally constant module-valued functions. -/
noncomputable def discreteModuleSectionsEquiv (S : LightProfinite) (M : ModuleCat ℤ) :
    ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨S⟩ ≃ LocallyConstant S M where
  toFun x := by
    let y := ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M).hom.app ⟨S⟩ x
    change LocallyConstant S M at y
    exact y
  invFun y := by
    let x : ((LightCondMod.LocallyConstant.functor ℤ).obj M).obj.obj ⟨S⟩ := y
    exact ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).hom.app M).hom.app ⟨S⟩ x
  left_inv x := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app M
    change (e.inv ≫ e.hom).hom.app ⟨S⟩ x = x
    rw [Iso.inv_hom_id]
    rfl
  right_inv y := by
    let e := (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app M
    change (e.hom ≫ e.inv).hom.app ⟨S⟩ y = y
    rw [Iso.hom_inv_id]
    rfl

/-- The locally constant-function description of discrete module sections is natural in the module. -/
lemma discreteModuleSectionsEquiv_map (S : LightProfinite) {M N : ModuleCat ℤ} (f : M ⟶ N)
    (x : ((LightCondensed.discrete (ModuleCat ℤ)).obj M).obj.obj ⟨S⟩) :
    discreteModuleSectionsEquiv S N (((LightCondensed.discrete (ModuleCat ℤ)).map f).hom.app ⟨S⟩ x) =
      (discreteModuleSectionsEquiv S M x).map f := by
  dsimp [discreteModuleSectionsEquiv]
  have hnatur := ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv).naturality f
  change (((LightCondensed.discrete (ModuleCat ℤ)).map f ≫
        (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app N).hom.app ⟨S⟩) x =
    (((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app M ≫
        (LightCondMod.LocallyConstant.functor ℤ).map f).hom.app ⟨S⟩) x
  simpa using congr_fun (congrArg (fun η => η.hom.app ⟨S⟩) hnatur) x

/-- The solidification of the sequence object `P ℤ`. -/
noncomputable abbrev solidP : Solid :=
  solidification.obj (P ℤ)

/-- The countable product of copies of `ℤ` in `Solid`. -/
noncomputable abbrev productInt : Solid :=
  solidProjectiveGenerator

/-- The underlying light condensed abelian group of the solid countable product of integers. -/
noncomputable abbrev productIntLight : LightCondAb :=
  (isSolid.ι).obj productInt

/-- The underlying light condensed abelian group of the solid countable product is the countable
product of the discrete integer sheaf. -/
noncomputable def productIntLightIsoProductZdisc :
    productIntLight ≅ ∏ᶜ fun _ : ℕ => Zdisc :=
  PreservesProduct.iso isSolid.ι (fun _ : ℕ => solidInteger)

@[simp]
lemma productIntLightIsoProductZdisc_hom_π (n : ℕ) :
    productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n =
      (Pi.π (fun _ : ℕ => solidInteger) n).hom := by
  change (piComparison isSolid.ι (fun _ : ℕ => solidInteger) ≫
      Pi.π (fun n : ℕ => (isSolid.ι).obj (solidInteger)) n) =
    (isSolid.ι).map (Pi.π (fun _ : ℕ => solidInteger) n)
  rw [piComparison_comp_π]

/-- Sections of an isomorphic pair of light condensed abelian groups are linearly equivalent. -/
noncomputable def sectionsLinearEquivOfIso {A B : LightCondAb} (e : A ≅ B)
    (S : LightProfinite) : A.obj.obj ⟨S⟩ ≃ₗ[ℤ] B.obj.obj ⟨S⟩ := by
  let a : A.obj.obj ⟨S⟩ ≃+ B.obj.obj ⟨S⟩ := {
    toFun := fun x => e.hom.hom.app ⟨S⟩ x
    invFun := fun y => e.inv.hom.app ⟨S⟩ y
    left_inv := by
      intro x
      change (e.hom ≫ e.inv).hom.app ⟨S⟩ x = x
      rw [e.hom_inv_id]
      rfl
    right_inv := by
      intro y
      change (e.inv ≫ e.hom).hom.app ⟨S⟩ y = y
      rw [e.inv_hom_id]
      rfl
    map_add' := by
      intro x y
      exact (e.hom.hom.app ⟨S⟩).hom.map_add x y }
  exact a.toIntLinearEquiv

/-- Sections of a countable product of copies of `Zdisc` are countable products of sections. -/
noncomputable def productZdiscSectionsEquiv (S : LightProfinite) :
    (∏ᶜ fun _ : ℕ => Zdisc).obj.obj ⟨S⟩ ≃ₗ[ℤ]
      (∀ _ : ℕ, Zdisc.obj.obj ⟨S⟩) := by
  let evS : LightCondAb ⥤ ModuleCat ℤ :=
    sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ) ⋙
      (evaluation LightProfiniteᵒᵖ (ModuleCat ℤ)).obj ⟨S⟩
  let e := PreservesProduct.iso evS (fun _ : ℕ => Zdisc) ≪≫
    ModuleCat.piIsoPi (fun _ : ℕ => evS.obj Zdisc)
  let coord : (∏ᶜ fun _ : ℕ => Zdisc).obj.obj ⟨S⟩ →
      (∀ _ : ℕ, Zdisc.obj.obj ⟨S⟩) :=
    fun x n => (Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩ x
  have hcoord : ∀ x, e.hom x = coord x := by
    intro x
    ext n
    letI : Module ℤ (∀ _ : ℕ, evS.obj Zdisc) :=
      Pi.module ℕ (fun _ : ℕ => evS.obj Zdisc) ℤ
    change (((PreservesProduct.iso evS (fun _ : ℕ => Zdisc)).hom ≫
      (ModuleCat.piIsoPi (fun _ : ℕ => evS.obj Zdisc)).hom) ≫ ModuleCat.ofHom
        (LinearMap.proj n : (∀ _ : ℕ, evS.obj Zdisc) →ₗ[ℤ] evS.obj Zdisc)).hom x =
      (Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩ x
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    change ((PreservesProduct.iso evS (fun _ : ℕ => Zdisc)).hom ≫
      Pi.π (fun _ : ℕ => evS.obj Zdisc) n).hom x =
      (Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩ x
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
    rfl
  let a : (∏ᶜ fun _ : ℕ => Zdisc).obj.obj ⟨S⟩ ≃+
      (∀ _ : ℕ, Zdisc.obj.obj ⟨S⟩) := {
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
      exact ((Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩).hom.map_add x y }
  exact a.toIntLinearEquiv

@[simp]
lemma productZdiscSectionsEquiv_apply (S : LightProfinite)
    (x : (∏ᶜ fun _ : ℕ => Zdisc).obj.obj ⟨S⟩) (n : ℕ) :
    productZdiscSectionsEquiv S x n =
      (Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩ x :=
  rfl

/-- The locally-constant-function description of `Zdisc`-sections as a linear equivalence. -/
noncomputable def zdiscSectionsLinearEquiv (S : LightProfinite) :
    Zdisc.obj.obj ⟨S⟩ ≃ₗ[ℤ] LocallyConstant S ℤ := by
  let a : Zdisc.obj.obj ⟨S⟩ ≃+ LocallyConstant S ℤ := {
    toFun := zdiscSectionsEquiv S
    invFun := (zdiscSectionsEquiv S).symm
    left_inv := (zdiscSectionsEquiv S).left_inv
    right_inv := (zdiscSectionsEquiv S).right_inv
    map_add' := by
      intro x y
      dsimp [zdiscSectionsEquiv]
      simp
      rfl }
  exact a.toIntLinearEquiv

/-- Sections of `productIntLight` are countable products of sections of `Zdisc`. -/
noncomputable def productIntSectionsEquiv (S : LightProfinite) :
    productIntLight.obj.obj ⟨S⟩ ≃ₗ[ℤ]
      (∀ _ : ℕ, Zdisc.obj.obj ⟨S⟩) :=
  (sectionsLinearEquivOfIso productIntLightIsoProductZdisc S).trans
    (productZdiscSectionsEquiv S)

@[simp]
lemma productIntSectionsEquiv_apply (S : LightProfinite)
    (x : productIntLight.obj.obj ⟨S⟩) (n : ℕ) :
    productIntSectionsEquiv S x n =
      ((productIntLightIsoProductZdisc.hom ≫
        Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩) x :=
  rfl

@[simp]
lemma productIntSectionsEquiv_symm_apply (S : LightProfinite)
    (x : ∀ _ : ℕ, Zdisc.obj.obj ⟨S⟩) (n : ℕ) :
    ((productIntLightIsoProductZdisc.hom ≫
        Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩)
      ((productIntSectionsEquiv S).symm x) = x n := by
  have h := congrFun (LinearEquiv.apply_symm_apply (productIntSectionsEquiv S) x) n
  rw [productIntSectionsEquiv_apply] at h
  exact h

/-- The sectionwise locally constant integer-valued function API for `productIntLight`. -/
noncomputable def productIntLocallyConstantSectionsEquiv (S : LightProfinite) :
    productIntLight.obj.obj ⟨S⟩ ≃ₗ[ℤ]
      (∀ _ : ℕ, LocallyConstant S ℤ) := by
  let a : productIntLight.obj.obj ⟨S⟩ ≃+ (∀ _ : ℕ, LocallyConstant S ℤ) := {
    toFun := fun x n => zdiscSectionsLinearEquiv S (productIntSectionsEquiv S x n)
    invFun := fun y => (productIntSectionsEquiv S).symm
      (fun n => (zdiscSectionsLinearEquiv S).symm (y n))
    left_inv := by
      intro x
      apply (productIntSectionsEquiv S).injective
      rw [LinearEquiv.apply_symm_apply]
      ext n
      simp
    right_inv := by
      intro y
      change (fun n => zdiscSectionsLinearEquiv S
          (productIntSectionsEquiv S
            ((productIntSectionsEquiv S).symm
              (fun n => (zdiscSectionsLinearEquiv S).symm (y n))) n)) = y
      rw [LinearEquiv.apply_symm_apply]
      ext n
      simp
    map_add' := by
      intro x y
      ext n s
      have h := congrFun ((productIntSectionsEquiv S).map_add x y) n
      rw [h]
      change (zdiscSectionsLinearEquiv S
          (productIntSectionsEquiv S x n + productIntSectionsEquiv S y n)) s =
        (zdiscSectionsLinearEquiv S (productIntSectionsEquiv S x n) +
          zdiscSectionsLinearEquiv S (productIntSectionsEquiv S y n)) s
      rw [map_add] }
  exact a.toIntLinearEquiv

@[simp]
lemma productIntLocallyConstantSectionsEquiv_apply (S : LightProfinite)
    (x : productIntLight.obj.obj ⟨S⟩) (n : ℕ) :
    productIntLocallyConstantSectionsEquiv S x n =
      zdiscSectionsEquiv S (productIntSectionsEquiv S x n) := by
  rfl

@[simp]
lemma productIntLocallyConstantSectionsEquiv_symm_apply (S : LightProfinite)
    (x : ∀ _ : ℕ, LocallyConstant S ℤ) (n : ℕ) :
    zdiscSectionsEquiv S
      (((productIntLightIsoProductZdisc.hom ≫
        Pi.π (fun _ : ℕ => Zdisc) n).hom.app ⟨S⟩)
          ((productIntLocallyConstantSectionsEquiv S).symm x)) = x n := by
  have h := congrFun
    (LinearEquiv.apply_symm_apply (productIntLocallyConstantSectionsEquiv S) x) n
  rw [productIntLocallyConstantSectionsEquiv_apply] at h
  exact h

lemma productIntSectionsEquiv_map {S S' : LightProfinite} (φ : S' ⟶ S)
    (x : productIntLight.obj.obj ⟨S⟩) :
    productIntSectionsEquiv S' (productIntLight.obj.map φ.op x) =
      fun n : ℕ => Zdisc.obj.map φ.op (productIntSectionsEquiv S x n) := by
  ext n
  rw [productIntSectionsEquiv_apply, productIntSectionsEquiv_apply]
  exact LightCondMod.hom_naturality_apply ℤ
    (productIntLightIsoProductZdisc.hom ≫ Pi.π (fun _ : ℕ => Zdisc) n) φ.op x

lemma productIntLocallyConstantSectionsEquiv_map {S S' : LightProfinite} (φ : S' ⟶ S)
    (x : productIntLight.obj.obj ⟨S⟩) :
    productIntLocallyConstantSectionsEquiv S' (productIntLight.obj.map φ.op x) =
      fun n : ℕ => (productIntLocallyConstantSectionsEquiv S x n).comap φ.hom.hom := by
  ext n
  rw [productIntLocallyConstantSectionsEquiv_apply,
    productIntLocallyConstantSectionsEquiv_apply]
  rw [productIntSectionsEquiv_map, zdiscSectionsEquiv_map]

end ProjectiveGeneratorProof
end Solid
end LightCondensed
