/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Condensed.Light.InternallyProjective
import LeanCondensed.Projects.LightProfiniteInjective
import LeanCondensed.Projects.PreservesCoprod
import LeanCondensed.Projects.Epi
import LeanCondensed.Mathlib.CategoryTheory.Countable
import LeanCondensed.Mathlib.Topology.Category.CompHausLike.Limits

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  CartesianMonoidalCategory Topology

universe u

section

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

def fibre : LightProfinite :=
  haveI : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  CompHausLike.of _ (f ⁻¹' {y})

def fibre_incl : fibre y f ⟶ X := ⟨{ toFun := Subtype.val }⟩

variable {Z : LightProfinite} {f : X ⟶ Z} {g : Y ⟶ Z}

instance [h : Epi f] : Epi (CompHausLike.pullback.snd f g) := by
  rw [LightProfinite.epi_iff_surjective] at h ⊢
  intro y
  obtain ⟨x, hx⟩ := h (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

end

variable (R : Type) [CommRing R]

@[simps!]
def CategoryTheory.Limits.parallelPairNatTrans {C : Type*} [Category C]
    {F G : WalkingParallelPair ⥤ C} (f0 : F.obj zero ⟶ G.obj zero)
    (f1 : F.obj one ⟶ G.obj one) (wl : F.map left ≫ f1 = f0 ≫ G.map left)
    (wr : F.map right ≫ f1 = f0 ≫ G.map right) : F ⟶ G where
  app | zero => f0 | one => f1
  naturality := by rintro _ _ ⟨_⟩ <;> simp [wl, wr]

def fibresOfOption {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) : Set T :=
  {t : T | (π t).2 = none} ∪ (⋃ (x : X), Set.range (σ x))

lemma fibresOfOption_closed {S T X : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] [DiscreteTopology X] [T2Space T] [CompactSpace S]
    (π : T → S × OnePoint X) (hπ : Continuous π)
    (σ : Option X → S → T) (hσ : ∀ x, Continuous (σ x))
    (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) :
    IsClosed (fibresOfOption π σ) := IsClosed.mk <| by
  have : IsOpen (⋃ i, (Set.range (σ (Option.some i)))ᶜ ∩ (Prod.snd ∘ π) ⁻¹' {(i : OnePoint X)}) := by
    refine isOpen_iUnion fun i ↦ IsOpen.inter ?_ ?_
    · simpa using IsCompact.isClosed (isCompact_range (hσ i))
    · refine .preimage (continuous_snd.comp hπ) ⟨fun h ↦ by simp_all, ?_⟩
      convert isOpen_discrete {i}
      aesop
  convert this
  ext x
  simp only [fibresOfOption, Set.compl_union, Set.compl_iUnion, Set.mem_inter_iff,
    Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_range, not_exists, Set.mem_iUnion,
    Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨n, hn, hn'⟩ ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h₁
    exact ⟨n, h₂ n, hn⟩
  · refine ⟨by simpa [hn'] using Option.isSome_iff_ne_none.mp rfl, fun i s h ↦ hn s ?_⟩
    rw [← h, hσ'] at hn'
    rw [← h, Option.some_injective _ hn'.symm]

def π_r {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) :
    fibresOfOption π σ → S × Option X :=
  fun x ↦ π x

def fibreInclGeneral {S T : Type*} (y : T) (f : S → T) : f ⁻¹' {y} → S := fun x ↦ x

def fibreIncl {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T) :
    (Prod.snd ∘ π_r π σ) ⁻¹' {none} → fibresOfOption π σ :=
  fibreInclGeneral none (Prod.snd ∘ π_r π σ)

lemma fibresOfOption_surjective {S T X : Type*}
    (π : T → S × Option X) (hπ : π.Surjective) (σ : Option X → S → T)
    (hσ : ∀ (x : Option X) s, (π (σ x s)).1 = s)
    (hσ' : ∀ (x : Option  X) (s : S), (π (σ x s)).2 = x) :
    (fun (x : fibresOfOption π σ) ↦ π x).Surjective := by
  rintro ⟨s, (rfl | x)⟩
  · obtain ⟨y, hy⟩ := hπ (s, none)
    exact ⟨⟨y, by simp [fibresOfOption, hy]⟩, hy⟩
  · exact ⟨⟨σ x s, by simp [fibresOfOption]⟩, Prod.ext (by grind) (by grind)⟩

abbrev smartCoverToFun {S T X Y : Type*} (i : Y → T) (π : T → S × Option X) :
    T ⊕ {xy : Y × Y // π (i xy.1) = π (i xy.2)} → {xy : T × T // π xy.1 = π xy.2} :=
  Sum.elim (fun t ↦ ⟨(t, t), rfl⟩) (fun xy ↦ ⟨(i xy.val.1, i xy.val.2), xy.prop⟩)

lemma smartCoverToFun_surjective {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (hσ : ∀ (x : Option X) s, (π (σ x s)).1 = s) (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) :
    Function.Surjective (smartCoverToFun (fibreIncl π σ) (π_r π σ)) := by
  intro ⟨⟨t, t'⟩, ht⟩
  dsimp [π_r] at ht
  have hht (x : X) (t : fibresOfOption π σ) (hn : x = (π t).2) : σ x (π t).1 = t := by
    have ht' := t.prop
    simp only [fibresOfOption, Set.mem_union] at ht'
    obtain (ht' | ht') := ht'
    · have ht' : (π t).2 = none := by dsimp at ht'; simp [← ht']
      simp_all
    · simp only [Set.mem_iUnion, Set.mem_range] at ht'
      obtain ⟨m, s, ht'⟩ := ht'
      rw [← ht', hσ m s, ← hσ' m s, hn, ← ht']
  by_cases h : (π t).2 = none
  · exact ⟨Sum.inr ⟨(⟨t, by grind [π_r]⟩, ⟨t', by grind [π_r]⟩),
      by simp [fibreIncl, fibreInclGeneral, π_r, ht]⟩,
      by simp [smartCoverToFun, fibreIncl, fibreInclGeneral]⟩
  · rw [← ne_eq, Option.ne_none_iff_exists'] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨Sum.inl ⟨σ n (π_r π σ t).1, by simp [fibresOfOption]⟩, ?_⟩
    simp only [Sum.elim_inl, Subtype.mk.injEq, Prod.mk.injEq]
    refine ⟨Subtype.ext <| hht _ _ hn.symm, ?_⟩
    rw [ht] at hn
    simpa [π_r, ht] using Subtype.ext <| hht _ _ hn.symm

abbrev smartCoverNew {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) :
    (CompHausLike.of _ (T ⊕ (CompHausLike.pullback (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)
      (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)))) ⟶ CompHausLike.pullback π π := ⟨{
  toFun := smartCoverToFun _ _
  continuous_toFun := by simpa using by fun_prop }⟩

def sectionOfFibreIncl {S T X : Type*} (π : T → S × Option X) (σ : Option X → S → T)
    (hσ' : ∀ (x : Option X) (s : S), (π (σ x s)).2 = x) : S → (Prod.snd ∘ π_r π σ) ⁻¹' {none} :=
  fun s ↦ ⟨⟨σ none s, by simp [fibresOfOption, hσ']⟩, by simp [hσ', π_r]⟩

lemma refinedCover {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ ℕ∪{∞}) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ ℕ∪{∞}) = g' ≫ π ∧
        IsSplitEpi (fibre_incl ∞ (π' ≫ snd S' ℕ∪{∞}) ≫ π' ≫ fst S' ℕ∪{∞}) ∧
          Epi (smartCoverNew π') := by
  have : Countable ℕ∪{∞} := inferInstanceAs (Countable <| Option _)
  have : CompactSpace
      {x : (n : ℕ∪{∞}) → fibre n (π ≫ snd _ _) | ∀ n m, (π (x n).val).1 = (π (x m).val).1} := by
    rw [← isCompact_iff_compactSpace, show
      {x : (n : ℕ∪{∞}) → fibre n (π ≫ snd _ _) | ∀ n m, (π (x n).val).1 = (π (x m).val).1} =
      ⋂ (n : ℕ∪{∞}) (m : ℕ∪{∞}), {x | (π (x n).val).1 = (π (x m).val).1} by aesop]
    refine (isClosed_iInter fun n ↦ isClosed_iInter fun m ↦ isClosed_eq ?_ ?_).isCompact
    all_goals exact continuous_fst.comp (Continuous.comp (by fun_prop) (continuous_subtype_val.comp
        ((continuous_apply _).comp (by fun_prop))))
  let S' : LightProfinite := LightProfinite.of
    {x : (n : ℕ∪{∞}) → fibre n (π ≫ snd _ _) | ∀ n m, (π (x n).val).1 = (π (x m).val).1}
  let S'π (n : ℕ∪{∞}) : S' ⟶ fibre n (π ≫ snd _ _) :=
    ⟨{ toFun x := x.val n, continuous_toFun := by refine (continuous_apply _).comp ?_; fun_prop }⟩
  let y' : S' ⟶ S := CompHausLike.ofHom _ {
    toFun x := (π (x.val none).val).1
    continuous_toFun := continuous_fst.comp <| Continuous.comp (by fun_prop) <|
      continuous_subtype_val.comp <| (continuous_apply _).comp <| by fun_prop }
  let Ttilde := CompHausLike.pullback π (y' ▷ ℕ∪{∞})
  let π_tilde : Ttilde ⟶ S' ⊗ ℕ∪{∞} := CompHausLike.pullback.snd _ _
  let σ' : ℕ∪{∞} → S' → Ttilde := fun n ↦ CompHausLike.pullback.lift _ _
    (S'π n ≫ fibre_incl _ _) (lift (𝟙 S') (CompHausLike.const _ n)) <| by
      apply CartesianMonoidalCategory.hom_ext
      · ext x; exact x.prop n none
      · ext x; exact (x.val n).prop
  have hσ (x : ℕ∪{∞}) (s : S') : (π_tilde (σ' x s)).1 = s := by simp [σ', π_tilde]; rfl
  have hσ' (x : ℕ∪{∞}) (s : S') : (π_tilde (σ' x s)).2 = x := by simp [σ', π_tilde]; rfl
  have : CompactSpace (fibresOfOption π_tilde σ') := isCompact_iff_compactSpace.mp
    (fibresOfOption_closed π_tilde (by fun_prop) σ' (by fun_prop) hσ').isCompact
  refine ⟨S', LightProfinite.of (fibresOfOption π_tilde σ'), y',
    ⟨⟨Subtype.val, by fun_prop⟩⟩ ≫ π_tilde,
    ⟨⟨Subtype.val, by fun_prop⟩⟩ ≫ CompHausLike.pullback.fst _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    refine fibresOfOption_surjective _ ?_ _ hσ hσ'
    rw [← LightProfinite.epi_iff_surjective]
    dsimp [π_tilde]
    infer_instance
  · rw [LightProfinite.epi_iff_surjective]
    intro y
    have : Function.Surjective π := by rwa [← LightProfinite.epi_iff_surjective]
    let p (s : S) (n : ℕ∪{∞}) : T := (this (s, n)).choose
    have hp (s : S) (n : ℕ∪{∞}) : π (p s n) = (s, n) := (this (s, n)).choose_spec
    refine ⟨⟨fun n ↦ ⟨p y n, ?_⟩, ?_⟩, ?_⟩
    · simp [hp]; rfl
    · simp [hp]
    · simp [y', hp]
  · simp [π_tilde, CompHausLike.pullback.condition]
  · exact ⟨⟨⟨sectionOfFibreIncl π_tilde σ' hσ', .subtype_mk (.subtype_mk (by fun_prop) _) _⟩⟩, rfl⟩
  · rw [LightProfinite.epi_iff_surjective]
    exact smartCoverToFun_surjective _ _ hσ hσ'

private lemma comm_sq {X Y : LightCondMod R} (p : X ⟶ Y) [hp : Epi p] {S : LightProfinite}
    (f : (free R).obj (S).toCondensed ⟶ Y) :
      ∃ (T : LightProfinite) (π : T ⟶ S) (g : ((free R).obj T.toCondensed) ⟶ X),
        Epi π ∧ (lightProfiniteToLightCondSet ⋙ (free R)).map π ≫ f = g ≫ p := by
  have : Epi ((LightCondensed.forget _).map p) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
  let y : Y.val.obj (op S) := (coherentTopology LightProfinite).yonedaEquiv <|
    (Adjunction.homEquiv (freeForgetAdjunction R) (S).toCondensed Y f)
  obtain ⟨T, π, hπ, x, hx⟩ := this S y
  let g : (free R).obj T.toCondensed ⟶ X :=
    ((freeForgetAdjunction R).homEquiv T.toCondensed X).symm
      ((coherentTopology LightProfinite).yonedaEquiv.symm x)
  refine ⟨T, π, g, (LightProfinite.epi_iff_surjective π).mpr hπ, ?_⟩
  rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_square_iff (freeForgetAdjunction R),
    Equiv.apply_symm_apply, Sheaf.hom_ext_iff,
    (coherentTopology LightProfinite).yonedaEquiv_symm_naturality_right, hx,
    (coherentTopology LightProfinite).map_yonedaEquiv',
    ← (coherentTopology LightProfinite).yonedaEquiv_symm_naturality_right]
  rfl

instance : IsLeftAdjoint (free R) := ⟨_, ⟨LightCondensed.freeForgetAdjunction R⟩⟩

noncomputable def hc {S T : LightProfinite} (π : T ⟶ S) [Epi π] :
    IsColimit ((free R).mapCocone (regular π)) :=
  isColimitOfPreserves _ (explicitRegularIsColimit _)

noncomputable def c {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ (S ⊗ ℕ∪{∞}))
    [Epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smartCoverNew π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (fibre ∞ (π ≫ snd _ _))) (σ : S ⟶ (fibre ∞ (π ≫ snd _ _)))
    (hr : fibre_incl ∞ (π ≫ snd _ _) ≫ r_inf = 𝟙 (fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
      (lightProfiniteToLightCondSet.map (CompHausLike.pullback.snd π π))) ⋙ (free R)) where
  pt := X
  ι :=  by
    let g_tilde : (lightProfiniteToLightCondSet ⋙ (free R)).obj T ⟶ X :=
      g -
        (lightProfiniteToLightCondSet ⋙ (free R)).map (r_inf ≫ fibre_incl ∞ (π ≫ snd _ _)) ≫ g +
        (lightProfiniteToLightCondSet ⋙ (free R)).map
          (r_inf ≫ fibre_incl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫ fibre_incl ∞ (π ≫ snd _ _)) ≫ g
    refine parallelPairNatTrans (_ ≫ g_tilde) g_tilde ?_ rfl
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smartCoverNew π)]
    apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ (free R))
        (CompHausLike.coprod.isColimit _ _)).hom_ext
    rintro ⟨⟨⟩⟩
    · simp [← Functor.map_comp_assoc, ← Functor.map_comp]
      rfl
    · simp only [comp_obj, pair_obj_right, const_obj_obj, mapCocone_pt, BinaryCofan.mk_pt,
        mapCocone_ι_app, BinaryCofan.mk_inr, Functor.comp_map, parallelPair_obj_zero,
        parallelPair_obj_one, parallelPair_map_left, ← map_comp_assoc, ← Functor.map_comp,
        parallelPair_map_right, const_obj_map, Category.comp_id]
      have : smartCoverNew π =
          CompHausLike.coprod.desc (CompHausLike.pullback.lift _ _ (𝟙 T) (𝟙 T) (by simp))
            (CompHausLike.pullback.lift _ _ ((CompHausLike.pullback.fst _ _) ≫ fibre_incl _ _)
              ((CompHausLike.pullback.snd _ _) ≫ fibre_incl _ _)
              (by simp [CompHausLike.pullback.condition])) := rfl
      simp only [this, CompHausLike.coprod.inr_desc_assoc, CompHausLike.pullback.lift_fst, comp_obj,
        Functor.comp_map, Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc,
        ← Functor.map_comp, Category.assoc, CompHausLike.pullback.lift_snd, g_tilde]
      simp only [← Functor.comp_map, ← Category.assoc, hr, Category.id_comp, sub_self, zero_add]
      simp [CompHausLike.pullback.condition]

instance (X Y : LightProfinite.{u}) [Nonempty X] : Epi (snd X Y) := by
  rw [LightProfinite.epi_iff_surjective]
  exact fun y ↦ ⟨⟨Nonempty.some inferInstance, y⟩, rfl⟩

theorem internallyProjective_ℕinfty : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R ℕ∪{∞}]
  intro X Y p hp S f
  obtain ⟨T, π, g, hπ, comm⟩ := comm_sq R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ := refinedCover π
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
    refine ⟨(LightProfinite.epi_iff_surjective _).mp inferInstance,
      (hc R π').desc (c R π' ((lightProfiniteToLightCondSet ⋙ (free R)).map g' ≫ g)
      r_inf split.section_ hr), ?_⟩
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π'),
      ← Functor.comp_map, ← Functor.map_comp_assoc]
    change _ = (((free R).mapCocone _).ι.app one ≫ (hc R π').desc (c R π' _ r_inf split.section_ hr)) ≫ p
    rw [(hc R π').fac]
    -- simp? [c, ← comm]:
    simp only [comp_obj, parallelPair_obj_one, Functor.comp_map, Functor.map_comp, Category.assoc,
      c, parallelPair_obj_zero, const_obj_obj, parallelPair_map_right, Lean.Elab.WF.paramLet,
      Preadditive.comp_add, Preadditive.comp_sub, parallelPairNatTrans_app, Preadditive.add_comp,
      Preadditive.sub_comp, ← comm]
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
  · have hh : IsEmpty (S' ⊗ ℕ∪{∞}) := { false a := IsEmpty.elim (by simpa using hS') (fst S' _ a) }
    have : IsIso π' := ⟨CompHausLike.ofHom _ ⟨(hh.elim ·), continuous_of_const <| by aesop⟩,
      by ext x; exact hh.elim (π' x), by ext x; all_goals exact hh.elim x⟩
    refine ⟨(LightProfinite.epi_iff_surjective _).mp inferInstance,
      (lightProfiniteToLightCondSet ⋙ (free R)).map (inv π' ≫ g') ≫ g, ?_⟩
    simp only [comp_obj, Functor.comp_map, Functor.map_comp, Functor.map_inv,
      Category.assoc, ← comm, ← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π'),
      IsIso.hom_inv_id_assoc]
    simp [← Category.assoc, ← Functor.map_comp, ← comp]
