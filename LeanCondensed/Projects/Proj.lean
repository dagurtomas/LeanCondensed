/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
-- import LeanCondensed.Projects.InternallyProjective
import Mathlib.Condensed.Light.InternallyProjective
import LeanCondensed.Projects.LightProfiniteInjective
import LeanCondensed.Projects.PreservesCoprod
import LeanCondensed.Projects.Epi
import LeanCondensed.Mathlib.CategoryTheory.Countable

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  CartesianMonoidalCategory Topology

universe u

section

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

def fibre : LightProfinite :=
  CompHausLike.pullback (CompHausLike.const (LightProfinite.of PUnit) y) f

def fibre_incl : fibre y f ⟶ X :=
  CompHausLike.pullback.snd (CompHausLike.const (LightProfinite.of PUnit) y) f

def fibreLift {Z : LightProfinite} (g : Z ⟶ X) (hg : ∀ z, f (g z) = y) : Z ⟶ fibre y f :=
  CompHausLike.pullback.lift _ _ (CompHausLike.const _ ()) g (by cat_disch)

@[simp]
lemma fibreLift_comp {Z : LightProfinite} (g : Z ⟶ X) (hg : ∀ z, f (g z) = y) :
    fibreLift y f g hg ≫ fibre_incl y f = g :=
  rfl

variable {X Y Z : LightProfinite} {f : X ⟶ Z} {g : Y ⟶ Z}

instance epi_pullback [hepi : Epi f] : Epi (CompHausLike.pullback.snd f g) := by
  rw [LightProfinite.epi_iff_surjective] at hepi ⊢
  intro y
  obtain ⟨x, hx⟩ := hepi (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

end

variable (R : Type) [CommRing R]

instance : TotallyDisconnectedSpace PUnit := by
  have := TotallySeparatedSpace.of_discrete
  apply TotallySeparatedSpace.totallyDisconnectedSpace

@[simps!]
def CategoryTheory.Limits.parallelPairNatTrans {C : Type*} [Category C]
    {F G : WalkingParallelPair ⥤ C} (f0 : F.obj zero ⟶ G.obj zero)
    (f1 : F.obj one ⟶ G.obj one) (wl : F.map left ≫ f1 = f0 ≫ G.map left)
    (wr : F.map right ≫ f1 = f0 ≫ G.map right) : F ⟶ G where
  app | zero => f0 | one => f1
  naturality := by rintro _ _ ⟨_⟩ <;> simp [wl, wr]

lemma isClosed_fibres {T : LightProfinite} (f : T ⟶ ℕ∪{∞}) (s : ℕ → Set T)
  (hs : ∀ n (x : s n), f x = n) (hs' : ∀ n, IsClosed (s n)) :
    IsClosed ({t | f t = ∞} ∪ ⋃ n, s n) := by
  apply IsClosed.mk
  have clopen (n : ℕ) : IsClopen (f ⁻¹' {(n : ℕ∪{∞})}) := by
    refine .preimage ⟨isClosed_singleton, ?_⟩ f.1.continuous
    exact ⟨fun h ↦ by simp_all, trivial⟩
  convert isOpen_iUnion (fun i ↦ IsOpen.inter (hs' i).1 (clopen i).2)
  ext x
  simp only [Set.compl_union, Set.compl_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro ⟨h₁, h₂⟩
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h₁
    exact ⟨n, h₂ n, hn⟩
  · intro ⟨n, hn, hn'⟩
    exact ⟨by simp [hn'], fun i hx ↦ by simp_all [hs i ⟨x, hx⟩]⟩



noncomputable def smart_cover {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) :
    coprod T (CompHausLike.pullback (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)
      (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)) ⟶ CompHausLike.pullback π π :=
  coprod.desc (CompHausLike.pullback.lift _ _ (𝟙 T) (𝟙 _) (by simp))
    (CompHausLike.pullback.lift _ _ (CompHausLike.pullback.fst _ _ ≫ fibre_incl _ _)
    (CompHausLike.pullback.snd _ _ ≫ fibre_incl _ _)
    (by simp [CompHausLike.pullback.condition]))

-- lemma subspaceCover_unbundled {S T X : Type*}

lemma subspaceCover { S T : LightProfinite } (π : T ⟶ S ⊗ ℕ∪{∞}) [hepi : Epi π]
    {σ' : ℕ∪{∞} → (S ⟶ T)} (hσ : ∀ n, σ' n ≫ π ≫ fst _ _ = 𝟙 _)
    (hσ' : ∀ n (s : S), (σ' n ≫ π ≫ snd S ℕ∪{∞}) s = n) : ∃ (T' : LightProfinite) (i : T' ⟶ T),
      Epi (i ≫ π) ∧ Epi (smart_cover (i ≫ π)) ∧ IsSplitEpi
        (fibre_incl ∞ ((i ≫ π) ≫ snd _ _) ≫ i ≫ π ≫ fst S ℕ∪{∞}) := by
  have : IsClosed ({t : T | (π ≫ snd _ _) t = ∞} ∪ (⋃ (n : ℕ), Set.range (σ' n))) :=
    isClosed_fibres _ _
      (fun n ⟨x, ⟨s, hs⟩⟩ ↦ by simp only [← hs, ← ConcreteCategory.comp_apply, hσ' _ _])
      (fun n ↦ IsCompact.isClosed (isCompact_range (σ' n).1.continuous))
  have compactSpace := isCompact_iff_compactSpace.mp this.isCompact
  let T' : LightProfinite := LightProfinite.of
      ({t : T | (π ≫ snd _ _) t = ∞} ∪ (⋃ (n : ℕ), Set.range (σ' n)) : Set T)
  let i : T' ⟶ T := CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
  have hht (n : ℕ) (t : T') (hn : n = (π t).2) : σ' n (π t).1 = t := by
    have ht' := t.prop
    rw [Set.mem_union] at ht'
    obtain (ht' | ht') := ht'
    · have ht' : (π t).2 = ∞ := by dsimp at ht'; simp [← ht']; rfl
      simp_all
    · simp only [Set.mem_iUnion, Set.mem_range] at ht'
      obtain ⟨m, s, ht'⟩ := ht'
      nth_rw 1 [← ht']
      have : (π (σ' m s)).1 = s := ConcreteCategory.hom_ext_iff.mp (hσ m) s
      convert ht'
      suffices (n : ℕ∪{∞}) = m by simpa using this
      rw [hn, ← ht']
      nth_rw 2 [← hσ' m s ]
      rfl
  refine ⟨T', i, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    rintro ⟨s, (rfl | n)⟩
    · obtain ⟨t, ht⟩ := (LightProfinite.epi_iff_surjective π).mp hepi ⟨s, none⟩
      exact ⟨⟨t, Or.inl <| by simp [ht]; rfl⟩, ht⟩
    · refine ⟨⟨σ' n s, by simp⟩, ?_⟩
      apply Prod.ext
      · change ConcreteCategory.hom (σ' n ≫ π ≫ fst _ _) s = s
        simp [hσ]
      · change ConcreteCategory.hom (σ' n ≫ π ≫ snd _ _) s = n
        rw [hσ']
  · rw [LightProfinite.epi_iff_surjective]
    intro ⟨⟨t, t'⟩, ht⟩
    replace ht : π t = π t' := by simpa [i] using ht
    by_cases h : (i ≫ π ≫ snd _ _) t = ∞
    · have : (i ≫ π ≫ snd _ _) t' = ∞ := by simp [← h, i, ht]
      let x : CompHausLike.pullback (fibre_incl ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) ≫ i ≫ π)
        (fibre_incl ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) ≫ i ≫ π) :=
        ⟨⟨⟨⟨(), t⟩, by simp [CompHausLike.const, i, ← this, ht]⟩, ⟨⟨(), t'⟩,
          by simp [CompHausLike.const, ← this]⟩⟩,
          by
            simp only [Set.mem_setOf_eq]
            rw [ConcreteCategory.comp_apply (fibre_incl _ _), ConcreteCategory.comp_apply
              (fibre_incl _ _)]
            unfold fibre_incl
            simp only [CompHausLike.const, CompHausLike.hom_ofHom]
            exact ht⟩
      let p := coprod.inr (X := T') (Y := (CompHausLike.pullback _ _)) x
      use coprod.inr (X := T') (Y := (CompHausLike.pullback _ _)) x
      rw [smart_cover, ← ConcreteCategory.comp_apply]
      simp
      rfl
    · rw [← ne_eq, OnePoint.ne_infty_iff_exists] at h
      obtain ⟨n, hn⟩ := h
      have hn : n = (π t).2 := by simpa using hn
      refine ⟨coprod.inl (X := T') (Y := (CompHausLike.pullback _ _)) ⟨σ' n (π (i t)).1, by simp⟩, ?_⟩
      simp only [smart_cover, ← ConcreteCategory.comp_apply, coprod.inl_desc]
      dsimp [CompHausLike.pullback.lift, i]
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact hht _ _ hn
      · apply Subtype.ext
        rw [ht] at hn
        simp only [ht]
        exact hht _ _ hn
  · let σ : (S ⟶ T') := CompHausLike.ofHom _ ⟨fun s ↦ ⟨σ' ∞ s, Or.inl (hσ' ∞ s)⟩, by continuity⟩
    have hhh := hσ' ∞
    refine ⟨fibreLift ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) σ (by exact hσ' ∞), ?_⟩
    simp only [← Category.assoc]
    rw [fibreLift_comp ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) σ (by exact hσ' ∞), show σ ≫ i = σ' ∞ from rfl,
     Category.assoc, hσ]

instance {J : Type*} [DecidableEq J] (B : LightProfinite.{u}) (objs : J → LightProfinite)
  (arrows: (j : J) → (objs j ⟶ B)) [hepi : ∀ j, Epi (arrows j)] [HasWidePullback B objs arrows] :
    ∀ j, Epi (WidePullback.π arrows j) := by
  intro i
  simp only [LightProfinite.epi_iff_surjective] at ⊢ hepi
  intro xi
  let point : LightProfinite.{u} := LightProfinite.of PUnit
  let base_pt : B := arrows i xi
  have choice : ∀ j, ∃ xj, arrows j xj = base_pt := fun j ↦ hepi j base_pt
  let point_maps : (j : J) → (point ⟶ objs j) := (fun j ↦
    if h : i = j then CompHausLike.ofHom _ (ContinuousMap.const point (h ▸ xi))
    else (CompHausLike.ofHom _ (ContinuousMap.const point (choice j).choose)))
  let lift : point ⟶ widePullback B objs arrows :=
    WidePullback.lift (CompHausLike.ofHom _ (ContinuousMap.const point base_pt)) point_maps
      (by
        intro j
        unfold point_maps
        by_cases h : i = j
        · rw [dif_pos h]
          subst h
          rfl
        · rw [dif_neg h]
          ext x
          simp only [ConcreteCategory.comp_apply, CompHausLike.hom_ofHom, ContinuousMap.const_apply]
          exact (choice j).choose_spec)
  use lift PUnit.unit
  rw [← ConcreteCategory.comp_apply, WidePullback.lift_π]
  simp [point_maps]

instance : DecidableEq ℕ∪{∞} := inferInstanceAs (DecidableEq <| Option ℕ)

lemma refinedCover {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ ℕ∪{∞}) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ ℕ∪{∞}) = g' ≫ π ∧
        IsSplitEpi (fibre_incl ∞ (π' ≫ snd S' ℕ∪{∞}) ≫ π' ≫ fst S' ℕ∪{∞}) ∧
          Epi (smart_cover π') := by
  have : Countable (WidePullbackShape ↑ℕ∪{∞}.toTop) :=
    inferInstanceAs (Countable <| Option (Option _))
  let S' := widePullback S (fun (n : ℕ∪{∞}) ↦ fibre n (π ≫ snd _ _))
    (fun n ↦ fibre_incl n (π ≫ snd _ _) ≫ π ≫ fst _ _)
  let y' : S' ⟶ S := WidePullback.base (fun n ↦ fibre_incl n (π ≫ snd _ _) ≫ π ≫ fst _ _)
  let Ttilde := CompHausLike.pullback π (y' ▷ ℕ∪{∞})
  let π_tilde : Ttilde ⟶ S' ⊗ ℕ∪{∞} := CompHausLike.pullback.snd _ _
  let σ' : ℕ∪{∞} → (S' ⟶ Ttilde) := fun n ↦
    CompHausLike.pullback.lift _ _
      ((WidePullback.π _ n) ≫ fibre_incl n (π ≫ snd _ _))
      (lift (𝟙 S') (CompHausLike.ofHom _ <| ContinuousMap.const S' n))
      (by
        simp only [Category.assoc, limit.cone_x]
        apply CartesianMonoidalCategory.hom_ext
        · simp [y']
        · ext
          simp only [Category.assoc, fibre_incl, ← CompHausLike.pullback.condition,
            lift_whiskerRight, Category.id_comp, lift_snd, CompHausLike.hom_ofHom,
            ContinuousMap.const_apply]
          rfl)
  obtain ⟨T', i, _, _, split⟩ := subspaceCover π_tilde (σ' := σ')
    (fun _ ↦ by simp [σ', π_tilde]) (fun _ _ ↦ by simp [σ', π_tilde])
  refine ⟨S', T', y', i ≫ π_tilde, i ≫ CompHausLike.pullback.fst _ _, inferInstance, ?_,
    by simp [π_tilde, CompHausLike.pullback.condition], split,
    inferInstance⟩
  dsimp [y']
  rw [← WidePullback.π_arrow _ (OnePoint.some 0)]
  have (j : ℕ∪{∞}) :Epi (fibre_incl j (π ≫ snd S ℕ∪{∞}) ≫ π ≫ fst S ℕ∪{∞}) := by
    rw [LightProfinite.epi_iff_surjective]
    intro s
    have : Function.Surjective π := by rw [← LightProfinite.epi_iff_surjective]; infer_instance
    obtain ⟨t, ht⟩ := this ⟨s, j⟩
    exact ⟨⟨⟨(), t⟩, by simp [ht]; rfl⟩, (Prod.ext_iff.mp ht).1⟩
  infer_instance

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
    [Epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smart_cover π)]
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
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smart_cover π)]
    apply (isColimitOfHasBinaryCoproductOfPreservesColimit
      (lightProfiniteToLightCondSet ⋙ (free R)) T
      (CompHausLike.pullback (fibre_incl ∞ (π ≫ snd _ _) ≫ π)
      (fibre_incl ∞ (π ≫ snd _ _) ≫ π))).hom_ext
    rintro ⟨⟨⟩⟩
    · simp [← Functor.map_comp_assoc, ← Functor.map_comp, smart_cover]
    · -- simp? [← map_comp_assoc, ← Functor.map_comp]:
      simp only [comp_obj, pair_obj_right, const_obj_obj, Functor.comp_map, BinaryCofan.mk_pt,
        BinaryCofan.mk_inr, parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left,
        ← map_comp_assoc, ← Functor.map_comp, parallelPair_map_right, const_obj_map,
        Category.comp_id]
      -- simp? [smart_cover, g_tilde]:
      simp only [smart_cover, coprod.desc_comp, CompHausLike.pullback.lift_fst, colimit.ι_desc,
        BinaryCofan.mk_pt, BinaryCofan.mk_inr, Functor.map_comp, comp_obj, Functor.comp_map,
        Category.assoc, Preadditive.comp_add, Preadditive.comp_sub, CompHausLike.pullback.lift_snd,
        g_tilde]
      -- simp? [← Functor.comp_map, ← Category.assoc, ← Functor.map_comp, hr]:
      simp only [← Functor.comp_map, ← Category.assoc, ← Functor.map_comp, hr, Category.id_comp,
        sub_self, zero_add]
      conv =>
        simp only [Category.assoc, Functor.comp_map]
        enter [1, 1, 2, 2]
        slice 1 3
        rw [CompHausLike.pullback.condition]
      rfl

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
      rintro ⟨⟨⟨⟩, _⟩, _⟩ _ rfl
      rfl
    have : Nonempty (fibre ∞ (π' ≫ snd _ _)) := by
      have : Epi (π' ≫ snd S' ℕ∪{∞}) := inferInstance
      obtain ⟨_, hx⟩ := (LightProfinite.epi_iff_surjective _).mp this ∞
      refine ⟨⟨(), _⟩, hx.symm⟩
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
      apply CartesianMonoidalCategory.hom_ext <;>
      simp [fibre_incl, ← CompHausLike.pullback.condition]
      rfl
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
