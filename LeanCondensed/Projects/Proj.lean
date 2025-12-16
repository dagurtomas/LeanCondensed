/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Condensed.Light.InternallyProjective
import Mathlib.Topology.FiberPartition
import LeanCondensed.Projects.LightProfiniteInjective
import LeanCondensed.Projects.PreservesCoprod
import LeanCondensed.Projects.Epi
import LeanCondensed.Mathlib.CategoryTheory.Countable
import LeanCondensed.Mathlib.Topology.Category.CompHausLike.Limits

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  CartesianMonoidalCategory Topology

universe u

variable (R : Type) [CommRing R]

-- TODO: put in the file about explicit limits in `CompHausLike`
instance {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) [h : Epi f] :
    Epi (CompHausLike.pullback.snd f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro y
  obtain ⟨x, hx⟩ := h (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

-- TODO: rename and put in the file about epimorphisms in light condensed sets/modules.
lemma comm_sq {X Y : LightCondMod R} (p : X ⟶ Y) [hp : Epi p] {S : LightProfinite}
    (f : (free R).obj (S).toCondensed ⟶ Y) :
      ∃ (T : LightProfinite) (π : T ⟶ S) (g : ((free R).obj T.toCondensed) ⟶ X),
        Epi π ∧ (lightProfiniteToLightCondSet ⋙ (free R)).map π ≫ f = g ≫ p := by
  have : Epi ((LightCondensed.forget _).map p) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
  obtain ⟨T, π, hπ, x, hx⟩ := this S <| (coherentTopology LightProfinite).yonedaEquiv <|
    (freeForgetAdjunction R).homEquiv S.toCondensed Y f
  refine ⟨T, π, ((freeForgetAdjunction R).homEquiv T.toCondensed X).symm
    ((coherentTopology LightProfinite).yonedaEquiv.symm x),
    (LightProfinite.epi_iff_surjective π).mpr hπ, ?_⟩
  rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_square_iff (freeForgetAdjunction R),
    Sheaf.hom_ext_iff, Equiv.apply_symm_apply,
    GrothendieckTopology.yonedaEquiv_symm_naturality_right, hx,
    GrothendieckTopology.map_yonedaEquiv', ← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  rfl

-- TODO: put in the file where the adjunction is defined
instance : IsLeftAdjoint (free R) := ⟨_, ⟨LightCondensed.freeForgetAdjunction R⟩⟩

-- TODO: put in the file that defines `ℕ∪{∞}`
instance : Countable ℕ∪{∞} := inferInstanceAs (Countable <| Option _)

namespace InternalProjectivityProof

-- TODO: give things shorter names and document the proof better.

section

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

def fibre : LightProfinite :=
  haveI : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  CompHausLike.of _ (f ⁻¹' {y})

def fibre_incl : fibre y f ⟶ X := ⟨{ toFun := Subtype.val }⟩

variable {Z : LightProfinite} {f : X ⟶ Z} {g : Y ⟶ Z}

end

def fibresOfOption {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) : Set T :=
  {t : T | (π t).2 = none} ∪ (⋃ (x : X), Set.range (σ x))

@[simp, grind =]
lemma mem_fibresOfOption_iff {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) (t : T) :
    t ∈ fibresOfOption π σ ↔ (π t).2 = none ∨ ∃ (x : X) (s : S), σ x s = t := by
  simp [fibresOfOption]

lemma fibresOfOption_compl_eq_iUnion {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) :
    (fibresOfOption π σ)ᶜ =
      ⋃ i, (Set.range (σ (Option.some i)))ᶜ ∩ (Prod.snd ∘ π) ⁻¹' {(i : OnePoint X)} := by
  ext x
  -- simp?:
  simp only [Set.mem_compl_iff, mem_fibresOfOption_iff, not_or, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, Function.comp_apply,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨n, hn, hn'⟩ ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h₁
    exact ⟨n, h₂ n, hn⟩
  · refine ⟨by simpa [hn'] using Option.isSome_iff_ne_none.mp rfl, fun i s h ↦ hn s ?_⟩
    rw [← h, hσ'] at hn'
    rw [← h, Option.some_injective _ hn'.symm]

lemma fibresOfOption_closed {S T X : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] [DiscreteTopology X] [T2Space T] [CompactSpace S]
    (π : T → S × OnePoint X) (hπ : Continuous π)
    (σ : Option X → S → T) (hσ : ∀ x, Continuous (σ x))
    (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) :
    IsClosed (fibresOfOption π σ) := IsClosed.mk <| by
  rw [fibresOfOption_compl_eq_iUnion π σ hσ']
  refine isOpen_iUnion fun i ↦ IsOpen.inter ?_ ?_
  · simpa using IsCompact.isClosed (isCompact_range (hσ i))
  · exact .preimage (continuous_snd.comp hπ) ⟨fun h ↦ by simp_all, by simp⟩

def π_r {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) :
    fibresOfOption π σ → S × Option X :=
  fun x ↦ π x

@[grind =]
lemma π_r_apply {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (x : fibresOfOption π σ) : π_r π σ x = π x :=
  rfl

def fibreInclGeneral {S T : Type*} (y : T) (f : S → T) : f ⁻¹' {y} → S := fun x ↦ x

def fibreIncl {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) :
    (Prod.snd ∘ π_r π σ) ⁻¹' {none} → fibresOfOption π σ :=
  fibreInclGeneral none (Prod.snd ∘ π_r π σ)

@[grind =]
lemma fibreIncl_apply {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (x : (Prod.snd ∘ π_r π σ) ⁻¹' {none}) : fibreIncl π σ x = x :=
  rfl

lemma fibresOfOption_surjective {S T X : Type*}
    (π : T → S × Option X) (hπ : π.Surjective) (σ : Option X → S → T)
    (hσ : ∀ (x : Option X) s, (π (σ x s)).1 = s)
    (hσ' : ∀ (x : Option  X) (s : S), (π (σ x s)).2 = x) :
    (fun (x : fibresOfOption π σ) ↦ π x).Surjective := by
  rintro ⟨s, (rfl | x)⟩
  · obtain ⟨y, hy⟩ := hπ (s, none)
    exact ⟨⟨y, by grind⟩, hy⟩
  · exact ⟨⟨σ x s, by simp⟩, Prod.ext (by grind) (by grind)⟩

def smartCoverToFun {S T X Y : Type*} (i : Y → T) (π : T → S × Option X) :
    T ⊕ {xy : Y × Y // π (i xy.1) = π (i xy.2)} → {xy : T × T // π xy.1 = π xy.2} :=
  Sum.elim (fun t ↦ ⟨(t, t), rfl⟩) (fun xy ↦ ⟨(i xy.val.1, i xy.val.2), xy.prop⟩)

@[grind =]
lemma smartCoverToFun_apply {S T X Y : Type*} (i : Y → T) (π : T → S × Option X)
    (t : T ⊕ {xy : Y × Y // π (i xy.1) = π (i xy.2)}) :
    smartCoverToFun i π t =
      Sum.elim (fun t ↦ ⟨(t, t), rfl⟩) (fun xy ↦ ⟨(i xy.val.1, i xy.val.2), xy.prop⟩) t :=
  rfl

lemma smartCoverToFun_surjective {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (hσ : ∀ (x : Option X) s, (π (σ x s)).1 = s) (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) :
    Function.Surjective (smartCoverToFun (fibreIncl π σ) (π_r π σ)) := by
  intro ⟨⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, _⟩
  by_cases h : (π t).2 = none
  · exact ⟨Sum.inr ⟨(⟨⟨t, ht⟩, by grind⟩, ⟨⟨t', ht'⟩, by grind⟩), by grind⟩, by grind⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨Sum.inl ⟨σ n (π t).1, by grind⟩, by grind⟩

def smartCoverNew {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) :
    (CompHausLike.of _ (T ⊕ (CompHausLike.pullback (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)
      (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)))) ⟶ CompHausLike.pullback π π := ⟨{
  toFun := smartCoverToFun _ _
  continuous_toFun := by dsimp [smartCoverToFun]; fun_prop }⟩

def sectionOfFibreIncl {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) : S → (Prod.snd ∘ π_r π σ) ⁻¹' {none} :=
  fun s ↦ ⟨⟨σ none s, by grind⟩, by grind⟩

def S' {S T X : Type*} (π : T → S × OnePoint X) :
    Set (∀ x : OnePoint X, (Prod.snd ∘ π) ⁻¹' {x}) :=
  {x | ∀ n m, (π (x n).val).1 = (π (x m).val).1}

@[simp, grind =]
lemma mem_S'_iff {S T X : Type*} (π : T → S × OnePoint X)
    (y : ∀ x : OnePoint X, (Prod.snd ∘ π) ⁻¹' {x}) : y ∈ S' π ↔
      ∀ n m, (π (y n).val).1 = (π (y m).val).1 :=
  Iff.rfl

def y {S T X : Type*} (π : T → S × OnePoint X) : S' π → S :=
  fun x ↦ (π (x.val ∞).val).1

@[simp]
lemma y_apply {S T X : Type*} (π : T → S × OnePoint X) (x : S' π) : y π x = (π (x.val ∞).val).1 :=
  rfl

lemma y_continuous {S T X : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] (π : T → S × OnePoint X) (hπ : Continuous π := by fun_prop) :
    Continuous (y π) :=
  continuous_fst.comp <| hπ.comp <| continuous_subtype_val.comp <|
    (continuous_apply _).comp (by fun_prop)

lemma S'_compactSpace {S T X : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace T]
    [CompactSpace T] [TopologicalSpace X] [T1Space (OnePoint X)]
    (π : T → S × OnePoint X) (hπ : Continuous π) : CompactSpace (S' π) := by
  rw [← isCompact_iff_compactSpace, show S' π =
    ⋂ (n : OnePoint X) (m : OnePoint X), {x | (π (x n).val).1 = (π (x m).val).1} by aesop]
  have (x : OnePoint X) : CompactSpace <| (Prod.snd ∘ π) ⁻¹' {x} :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  refine (isClosed_iInter fun n ↦ isClosed_iInter fun m ↦ isClosed_eq ?_ ?_).isCompact
  all_goals fun_prop

@[simps! pt ι_app]
noncomputable def c {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ (S ⊗ ℕ∪{∞}))
    [Epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smartCoverNew π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (fibre ∞ (π ≫ snd _ _))) (σ : S ⟶ (fibre ∞ (π ≫ snd _ _)))
    (hr : fibre_incl ∞ (π ≫ snd _ _) ≫ r_inf = 𝟙 (fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
      (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π))) ⋙ (free R)) := by
  refine Cocone.ofCofork (Cofork.ofπ (g -
    (lightProfiniteToLightCondSet ⋙ (free R)).map (r_inf ≫ fibre_incl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ (free R)).map
      (r_inf ≫ fibre_incl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫ fibre_incl ∞ (π ≫ snd _ _)) ≫ g) ?_)
  rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smartCoverNew π)]
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ (free R))
      (CompHausLike.coproductIsColimit _ _)).hom_ext
  rintro ⟨⟨⟩⟩
  · simp [← Functor.map_comp_assoc, -Functor.map_comp]
    rfl
  · -- simp? [← map_comp_assoc, -Functor.map_comp]:
    simp only [comp_obj, pair_obj_right, mapCocone_pt, const_obj_obj, mapCocone_ι_app,
      Functor.comp_map, parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left,
      Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc, parallelPair_map_right]
    have : smartCoverNew π = (BinaryCofan.IsColimit.desc' (CompHausLike.coproductIsColimit _ _)
        (CompHausLike.pullback.lift _ _ (𝟙 T) (𝟙 T) (by simp))
        (CompHausLike.pullback.lift _ _ ((CompHausLike.pullback.fst _ _) ≫ fibre_incl _ _)
          ((CompHausLike.pullback.snd _ _) ≫ fibre_incl _ _)
          (by simp [CompHausLike.pullback.condition]))).val := rfl
    -- simp? [this, ← Functor.map_comp]:
    simp only [this, pair_obj_left, const_obj_obj, pair_obj_right, BinaryCofan.IsColimit.desc'_coe,
      IsColimit.fac, BinaryCofan.mk_pt, BinaryCofan.mk_inr, ← Functor.map_comp,
      CompHausLike.pullback.lift_fst, IsColimit.fac_assoc, Category.assoc,
      CompHausLike.pullback.lift_snd]
    -- simp? [-Functor.map_comp, ← Category.assoc, hr]:
    simp only [← Category.assoc, hr, Category.id_comp, sub_self, zero_add]
    simp [CompHausLike.pullback.condition]

instance (X Y : LightProfinite.{u}) [Nonempty X] : Epi (snd X Y) := by
  rw [LightProfinite.epi_iff_surjective]
  exact fun y ↦ ⟨⟨Nonempty.some inferInstance, y⟩, rfl⟩

lemma aux {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ ℕ∪{∞}) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ ℕ∪{∞}) = g' ≫ π ∧
        IsSplitEpi (fibre_incl ∞ (π' ≫ snd S' ℕ∪{∞}) ≫ π' ≫ fst S' ℕ∪{∞}) ∧
          Epi (smartCoverNew π') := by
  have := S'_compactSpace π (by fun_prop)
  let S'π (n : ℕ∪{∞}) : LightProfinite.of (S' π) ⟶ fibre n (π ≫ snd _ _) :=
    ⟨{ toFun x := x.val n, continuous_toFun := by refine (continuous_apply _).comp ?_; fun_prop }⟩
  let y' : LightProfinite.of (S' π) ⟶ S := ConcreteCategory.ofHom ⟨y π, y_continuous π⟩
  let π' := CompHausLike.pullback.snd π (y' ▷ ℕ∪{∞})
  let σ' : ℕ∪{∞} → LightProfinite.of (S' π) → CompHausLike.pullback π (y' ▷ ℕ∪{∞}) :=
    fun n ↦ CompHausLike.pullback.lift _ _
      (S'π n ≫ fibre_incl _ _) (lift (𝟙 _) (CompHausLike.const _ n)) <| by
        apply CartesianMonoidalCategory.hom_ext
        · ext x; exact x.prop n ∞
        · ext x; exact (x.val n).prop
  have hσ (x : ℕ∪{∞}) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).1 = s := rfl
  have hσ' (x : ℕ∪{∞}) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).2 = x := rfl
  have : CompactSpace (fibresOfOption π' σ') := isCompact_iff_compactSpace.mp
    (fibresOfOption_closed π' (by fun_prop) σ' (by fun_prop) hσ').isCompact
  refine ⟨LightProfinite.of (S' π), LightProfinite.of (fibresOfOption π' σ'), y',
    ⟨⟨Subtype.val, by fun_prop⟩⟩ ≫ π',
    ⟨⟨Subtype.val, by fun_prop⟩⟩ ≫ CompHausLike.pullback.fst _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    refine fibresOfOption_surjective _ ?_ _ hσ hσ'
    rw [← LightProfinite.epi_iff_surjective]
    dsimp [π']
    infer_instance
  · rw [LightProfinite.epi_iff_surjective]
    intro y
    have : Function.Surjective π := by rwa [← LightProfinite.epi_iff_surjective]
    let p (s : S) (n : ℕ∪{∞}) : T := (this (s, n)).choose
    have hp (s : S) (n : ℕ∪{∞}) : π (p s n) = (s, n) := (this (s, n)).choose_spec
    exact ⟨⟨fun n ↦ ⟨p y n, by grind⟩, by grind⟩, by simp [y', hp]⟩
  · simp [π', CompHausLike.pullback.condition]
  · exact ⟨ConcreteCategory.ofHom ⟨(sectionOfFibreIncl π' σ' hσ'),
      (.subtype_mk (.subtype_mk (by fun_prop) _) _)⟩, rfl⟩
  · rw [LightProfinite.epi_iff_surjective]
    exact smartCoverToFun_surjective _ _ hσ hσ'

end InternalProjectivityProof

open InternalProjectivityProof

theorem LightCondensed.internallyProjective_free_natUnionInfty :
    InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R ℕ∪{∞}]
  intro X Y p hp S f
  obtain ⟨T, π, g, hπ, comm⟩ := comm_sq R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ := aux π
  refine ⟨S', y', ?_⟩
  by_cases hS' : Nonempty S'
  · have : Mono (fibre_incl ∞ (π' ≫ snd _ _)) := by
      rw [CompHausLike.mono_iff_injective]
      simp [fibre_incl]
      exact Subtype.val_injective
    have : Nonempty (fibre ∞ (π' ≫ snd _ _)) := by
      have : Epi (π' ≫ snd S' ℕ∪{∞}) := inferInstance
      obtain ⟨x, hx⟩ := (LightProfinite.epi_iff_surjective _).mp this ∞
      refine ⟨x, by simpa using hx⟩
    obtain ⟨r_inf, hr⟩ := Injective.factors (𝟙 _) (fibre_incl ∞ (π' ≫ snd _ _))
    have hc := isColimitOfPreserves (free R) (explicitRegularIsColimit π')
    refine ⟨(LightProfinite.epi_iff_surjective _).mp inferInstance,
      hc.desc (c R π' ((lightProfiniteToLightCondSet ⋙ (free R)).map g' ≫ g)
      r_inf split.section_ hr), ?_⟩
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π'),
      ← Functor.comp_map, ← Functor.map_comp_assoc]
    change _ = (((free R).mapCocone _).ι.app one ≫ hc.desc (c R π' _ r_inf split.section_ hr)) ≫ p
    rw [hc.fac]
    -- simp? [← comm]:
    simp only [comp_obj, parallelPair_obj_one, Functor.comp_map, Functor.map_comp, Category.assoc,
      c_pt, c_ι_app, eqToHom_refl, Preadditive.comp_add, Preadditive.comp_sub, Category.id_comp,
      Preadditive.add_comp, Preadditive.sub_comp, ← comm]
    simp only [← Functor.map_comp, ← Functor.comp_map, ← Category.assoc, ← comp]
    symm
    rw [sub_add, sub_eq_self, sub_eq_zero]
    simp only [Category.assoc]
    have : fibre_incl ∞ (π' ≫ snd _ _) ≫ π' = fibre_incl ∞ (π' ≫ snd _ _) ≫ π' ≫ fst _ _ ≫
        lift (𝟙 _) (CompHausLike.const S' (∞ : ℕ∪{∞})) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [fibre_incl]
      · ext a
        exact a.prop
    rw [reassoc_of% this, reassoc_of% split.id]
  · have hh : IsEmpty (S' ⊗ ℕ∪{∞}) := isEmpty_prod.mpr <| Or.inl <| by simpa using hS'
    have : IsIso π' := ⟨ConcreteCategory.ofHom ⟨(hh.elim ·), continuous_of_const <| by aesop⟩,
      by ext x; exact hh.elim (π' x), by ext x; all_goals exact hh.elim x⟩
    refine ⟨(LightProfinite.epi_iff_surjective _).mp inferInstance,
      (lightProfiniteToLightCondSet ⋙ (free R)).map (inv π' ≫ g') ≫ g, ?_⟩
    -- simp? [← comm, ← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π')]:
    simp only [comp_obj, Functor.comp_map, Functor.map_comp, Functor.map_inv, Category.assoc,
      ← comm, ← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π'),
      IsIso.hom_inv_id_assoc]
    simp [← Category.assoc, ← Functor.map_comp, ← comp]
