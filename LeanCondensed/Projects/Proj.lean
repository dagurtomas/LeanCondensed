import LeanCondensed.Projects.Initial
import LeanCondensed.Projects.InternallyProjective
import LeanCondensed.Projects.LightProfiniteInjective
import LeanCondensed.Projects.PreservesCoprod
import LeanCondensed.Projects.Pullbacks

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom
  CartesianMonoidalCategory Topology

universe u

variable (R : Type) [CommRing R]

instance : TotallyDisconnectedSpace PUnit := by
  have := TotallySeparatedSpace.of_discrete
  apply TotallySeparatedSpace.totallyDisconnectedSpace

@[simps!]
def CategoryTheory.Limits.parallelPairNatTrans {C : Type*} [Category C]
    {F G : WalkingParallelPair ⥤ C} (f0 : F.obj zero ⟶ G.obj zero)
    (f1 : F.obj one ⟶ G.obj one) (wl : F.map left ≫ f1 = f0 ≫ G.map left)
    (wr : F.map right ≫ f1 = f0 ≫ G.map right) : F ⟶ G := {
      app j := match j with
      | zero => f0
      | one => f1
      naturality := by
        rintro _ _ ⟨_⟩ <;>
        simp [wl, wr] }

lemma isClosed_fibres {T : LightProfinite} (f : T ⟶ ℕ∪{∞}) (s : ℕ → Set T)
  (hs : ∀ n (x : s n), f x = n) (hs' : ∀ n, IsClosed (s n)) :
    IsClosed ({t | f t = ∞} ∪ ⋃ n, s n) := by
  apply IsClosed.mk
  let fibre : ℕ → Set T := fun n ↦ f ⁻¹' {OnePoint.some n}
  have clopen : ∀ n, IsClopen (fibre n) := by
    intro n
    refine IsClopen.preimage ⟨isClosed_singleton, ?_⟩ f.1.continuous
    exact ⟨fun h ↦ by simp_all, trivial⟩

  suffices ({t | f t = ∞} ∪ ⋃ n, s n)ᶜ = ⋃ n, (s n)ᶜ ∩ fibre n by
    rw [this]
    exact isOpen_iUnion (fun i ↦ IsOpen.inter (hs' i).1 (clopen i).2)

  ext x
  simp only [Set.compl_union, Set.compl_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
    Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨n', hn⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨n', h' n', hn⟩
  · intro ⟨n, hn, hn'⟩
    refine ⟨?_, ?_⟩
    · rw [hn']
      exact OnePoint.coe_ne_infty _
    intro i
    by_cases h : i = n
    exact h ▸ hn
    intro h'
    have := hs i ⟨x, h'⟩
    apply h
    rw [hn', OnePoint.coe_eq_coe,] at this
    exact Eq.symm this


set_option maxHeartbeats 500000
noncomputable def smart_cover {S T : LightProfinite} (π : T ⟶ S ⊗ ℕ∪{∞}) :
    coprod T (explicitPullback (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)
      (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)) ⟶ explicitPullback π π :=
  coprod.desc
    (explicitPullback.diagonal π : T ⟶ explicitPullback π π)
    (explicitPullback.map
      (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π) (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π) π π
        (fibre_incl ∞ (π ≫ snd S ℕ∪{∞})) (fibre_incl ∞ (π ≫ snd S ℕ∪{∞})) (𝟙 _)
        (by rw [Category.comp_id]) (by rw [Category.comp_id]) :
          explicitPullback (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π)
          (fibre_incl ∞ (π ≫ snd S ℕ∪{∞}) ≫ π) ⟶ explicitPullback π π)

lemma subspaceCover { S T : LightProfinite } (π : T ⟶ S ⊗ ℕ∪{∞}) [hepi : Epi π]
    {σ' : ℕ∪{∞} → (S ⟶ T)} (hσ : ∀ n, σ' n ≫ π ≫ fst _ _ = 𝟙 _)
    (hσ' : ∀ n s, (σ' n ≫ π ≫ snd S ℕ∪{∞}) s = ↑n) : ∃ (T' : LightProfinite) (i : T' ⟶ T),
      Epi (i ≫ π) ∧ Epi (smart_cover (i ≫ π)) ∧ IsSplitEpi
        (fibre_incl ∞ ((i ≫ π) ≫ snd _ _) ≫ i ≫ π ≫ fst S ℕ∪{∞}) := by
  let space : Set T :=
    Set.iUnion (fun (n : ℕ) ↦ Set.range (σ' (OnePoint.some n))) ∪ {t : T | (π ≫ snd _ _) t = ∞}
  have : IsClosed space := by
    unfold space
    rw [Set.union_comm]
    exact isClosed_fibres _ _
      (fun n ⟨x, ⟨s, hs⟩⟩ ↦ by simp only [← hs, ← ConcreteCategory.comp_apply, hσ' _ _])
      (fun n ↦ IsCompact.isClosed (isCompact_range (σ' n).1.continuous))

  let T' : LightProfinite := ⟨TopCat.of space, inferInstance, inferInstance⟩

  let i : T' ⟶ T :=
    CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

  have : Mono i := by
    rw [CompHausLike.mono_iff_injective]
    exact Subtype.val_injective

  let σ : ℕ∪{∞} → (S ⟶ T') := fun n ↦ (CompHausLike.ofHom _
    ⟨fun s ↦ ⟨σ' n s,
      by
        rcases n with (n | n)
        · exact Or.inr (hσ' ∞ s)
        · apply Or.inl
          rw [Set.mem_iUnion]
          exact ⟨n, s, rfl⟩⟩,
      by continuity⟩)

  have hσ'' : ∀ (n : ℕ∪{∞}) (t : T'), t ∈ Set.range (σ n) → (i ≫ π ≫ fst _ _ ≫ σ n) t = t := by
    intro n t ht
    obtain ⟨s, hs⟩ := ht
    rw (config := { occs := .pos [1]}) [←hs]
    rw [← ConcreteCategory.comp_apply, ← Category.assoc π, ← Category.assoc i,
      ← Category.assoc (σ n)]
    erw [hσ]
    rw [Category.id_comp, hs]

  have coe_i : ∀ (t : T'), ↑t = i t := fun _ ↦ rfl
  have σ_i : ∀ n, σ' n = σ n ≫ i := fun _ ↦ rfl

  have hT' : ∀ (n : ℕ) t, t ∈ Set.range (σ n) ↔ (i ≫ π ≫ snd _ _) t = n := by
    intro n t'
    constructor <;> intro h
    · obtain ⟨_, ht⟩ := h
      rw [←ht, ←ConcreteCategory.comp_apply]
      erw [hσ']
    · rcases t'.2 with (fin | inf)
      · rw [Set.mem_iUnion] at fin
        obtain ⟨j, ⟨s, hs⟩⟩ := fin
        suffices h' : j = n by
          rw [h'] at hs
          use s
          exact Subtype.ext hs
        rw [coe_i] at hs
        rw [ConcreteCategory.comp_apply, ←hs, ←ConcreteCategory.comp_apply, hσ'] at h
        rw [←OnePoint.coe_eq_coe]
        exact h
      · simp only [Set.mem_setOf_eq] at inf
        erw [inf] at h
        exact (Option.some_ne_none n (Eq.symm h)).elim

  refine ⟨T', i, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    rintro ⟨s, (n | n)⟩
    · obtain ⟨t, ht⟩ := (LightProfinite.epi_iff_surjective π).mp hepi ⟨s, none⟩
      have : t ∈ space := by
        apply Or.inr
        rw [Set.mem_setOf_eq, ConcreteCategory.comp_apply, ht]
        rfl
      use ⟨t, this⟩
      rw [← ht]
      rfl
    · use σ n s
      apply Prod.ext
      change ConcreteCategory.hom (σ' n ≫ π ≫ fst _ _) s = s
      rw [hσ]; rfl
      change ConcreteCategory.hom (σ' n ≫ π ≫ snd _ _) s = (OnePoint.some n)
      rw [hσ']
  · rw [LightProfinite.epi_iff_surjective]
    intro ⟨⟨t,t'⟩, ht⟩
    by_cases h : (i ≫ π ≫ snd _ _) t = ∞
    · have : (i ≫ π ≫ snd _ _) t' = ∞ := by
        rw [←Category.assoc, ConcreteCategory.comp_apply, ←ht,
          ←ConcreteCategory.comp_apply, Category.assoc, h
        ]
      let x : explicitPullback (fibre_incl ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) ≫ i ≫ π)
        (fibre_incl ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) ≫ i ≫ π) :=
        ⟨⟨⟨t, h⟩, ⟨t', this⟩⟩, by
          simp only [Set.mem_setOf_eq]
          rw [ConcreteCategory.comp_apply (fibre_incl _ _), ConcreteCategory.comp_apply
            (fibre_incl _ _)]
          unfold fibre_incl
          simp only [CompHausLike.hom_ofHom, ContinuousMap.coe_mk]
          exact ht⟩
      let p := coprod.inr (X := T') (Y := (explicitPullback _ _)) x
      use coprod.inr (X := T') (Y := (explicitPullback _ _)) x
      rw [smart_cover, ←ConcreteCategory.comp_apply]
      simp only [coprod.inr_desc]
      rfl
    · rw [←ne_eq, OnePoint.ne_infty_iff_exists] at h
      obtain ⟨n, hn⟩ := h
      symm at hn
      use coprod.inl (X := T') (Y := (explicitPullback _ _)) ((i ≫ π ≫ fst _ _ ≫ σ n) t)
      simp only [smart_cover, ← ConcreteCategory.comp_apply, Category.assoc, coprod.inl_desc]
      rw [← Category.assoc (fst _ _), ← Category.assoc π,  ← Category.assoc i,
        ConcreteCategory.comp_apply
      ]
      rw [hσ'']
      · apply Subtype.ext
        apply Prod.ext (by rfl)
        change t = t'
        have hn' : (ConcreteCategory.hom (i ≫ π ≫ snd S ℕ∪{∞})) t' = n := by
          rw [←hn, ← Category.assoc, ConcreteCategory.comp_apply,
            ConcreteCategory.comp_apply (i ≫ π), ht]
        rw [← hT'] at hn hn'
        obtain ⟨s, hs⟩ := hn
        obtain ⟨s', hs'⟩ := hn'
        rw [← hs, ← hs']
        apply congr_arg
        rw [← ConcreteCategory.id_apply s, ← ConcreteCategory.id_apply s']
        erw [← hσ n, σ_i]
        simp only [Category.assoc]
        erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply (σ n), hs, hs']
        erw [← Category.assoc, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply (i ≫ π), ht]
        rfl
      · exact (hT' _ _).mpr hn
  · have : σ ∞ ≫ i = σ' ∞ := rfl
    let σσ : S ⟶ fibre ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) :=
      fibreLift ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) (σ ∞) (by exact hσ' ∞)
    exact ⟨⟨σσ, by
      simp only [←Category.assoc]
      rw [fibreLift_comp ∞ ((i ≫ π) ≫ snd S ℕ∪{∞}) (σ ∞) (by exact hσ' ∞)]
      erw [hσ]⟩⟩

lemma refinedCover { S T : LightProfinite } (π : T ⟶ S ⊗ ℕ∪{∞}) [Epi π] :
    ∃ (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' ⊗ ℕ∪{∞}) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ MonoidalCategoryStruct.tensorHom y' (𝟙 _) = g' ≫ π ∧
        IsSplitEpi (fibre_incl ∞ (π' ≫ snd S' ℕ∪{∞}) ≫ π' ≫ fst S' ℕ∪{∞}) ∧
          Epi (smart_cover π') := by
  have : Countable (WidePullbackShape ↑ℕ∪{∞}.toTop) := by
    have : Countable ℕ∪{∞} := Option.instCountable
    apply Option.instCountable
  let S' := widePullback S (fun (n : ℕ∪{∞}) ↦ fibre n (π ≫ snd _ _))
    (fun n ↦ fibre_incl n (π ≫ snd _ _) ≫ π ≫ fst _ _)
  let y' : S' ⟶ S := WidePullback.base (fun n ↦ fibre_incl n (π ≫ snd _ _) ≫ π ≫ fst _ _)


  let Ttilde := explicitPullback π (MonoidalCategoryStruct.tensorHom y' (𝟙 ℕ∪{∞}))
  let π_tilde : Ttilde ⟶ S' ⊗ ℕ∪{∞} := explicitPullback.snd _ _

  let σ' : ℕ∪{∞} → (S' ⟶ Ttilde) := fun n ↦
    PullbackCone.IsLimit.lift explicitPullback.IsLimit
      ((WidePullback.π _ n) ≫ fibre_incl n (π ≫ snd _ _))
      (lift (𝟙 S') (CompHausLike.ofHom _ <| ContinuousMap.const S' n))
      (by
        simp only [Category.assoc, limit.cone_x]
        apply CartesianMonoidalCategory.hom_ext
        · simp [y']
        · ext
          simp only [Category.assoc, fibre_condition, tensorHom_id, lift_whiskerRight,
            Category.id_comp, lift_snd, CompHausLike.hom_ofHom, ContinuousMap.const_apply]
          rfl)
  have hσ : ∀ n, σ' n ≫ π_tilde ≫ fst _ _ = 𝟙 _ := by
    intro n
    simp only [←Category.assoc, σ']
    erw [PullbackCone.IsLimit.lift_snd]
    exact lift_fst _ _
  have hσ' : ∀ n s, (σ' n ≫ π_tilde ≫ snd S' ℕ∪{∞}) s = n := by
    intro n s
    simp only [←Category.assoc, σ']
    erw [PullbackCone.IsLimit.lift_snd]
    simp

  obtain ⟨T', i, _, _, split⟩ := subspaceCover π_tilde hσ hσ'

  refine ⟨S', T', y', i ≫ π_tilde, i ≫ explicitPullback.fst _ _, inferInstance, ?_, ?_, split,
    inferInstance⟩
  · unfold y'
    rw [←WidePullback.π_arrow _ (OnePoint.some 0)]
    have : ∀ j, Epi (fibre_incl j (π ≫ snd S ℕ∪{∞}) ≫ π ≫ fst S ℕ∪{∞}) := by
      simp_rw [LightProfinite.epi_iff_surjective]
      intro j s
      have epi : Epi π := inferInstance
      rw [LightProfinite.epi_iff_surjective] at epi
      obtain ⟨t, ht⟩ := epi ⟨s, j⟩
      use ⟨t, by
        simp only [Set.mem_preimage, ConcreteCategory.comp_apply, ht,
          Set.mem_singleton_iff]
        rfl⟩
      rw [ConcreteCategory.comp_apply]
      change (ConcreteCategory.hom (π ≫ fst S ℕ∪{∞})) t = s
      rw [ConcreteCategory.comp_apply, ht]
      rfl
    have := surj_widePullback S (fun (n : ℕ∪{∞}) ↦ fibre n (π ≫ snd _ _))
      (fun n ↦ fibre_incl n (π ≫ snd _ _) ≫ π ≫ fst _ _) this
    apply epi_comp
  simp only [π_tilde, Category.assoc,explicitPullback.condition]

section

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

instance (S : Set Y) [IsClosed S] : IsClosed (f ⁻¹' S) := by
  exact IsClosed.preimage f.1.continuous inferInstance

instance : IsClosed (f ⁻¹' {y}) :=
  inferInstance

instance (S : Set X) [IsClosed S] : CompactSpace S := by
  exact isCompact_iff_compactSpace.mp (IsClosed.isCompact inferInstance)

instance : CompactSpace (f ⁻¹' {y}) := inferInstance
end


lemma prod_epi (X Y : LightProfinite.{u}) [hempty : Nonempty X] : Epi (snd X Y) := by
  rw [LightProfinite.epi_iff_surjective]
  exact fun y ↦ ⟨⟨Classical.choice hempty, y⟩, rfl⟩

private lemma comm_sq {X Y : LightCondMod R} (p : X ⟶ Y) [hp : Epi p] {S : LightProfinite}
  (f : (free R).obj (S).toCondensed ⟶ Y)
    : ∃ (T : LightProfinite) (π : T ⟶ S) (g : ((free R).obj T.toCondensed) ⟶ X), Epi π
      ∧ g ≫ p = (lightProfiniteToLightCondSet ⋙ (free R)).map π ≫ f := by
  have : Epi ((LightCondensed.forget _).map p) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this

  let y : Y.val.obj (op S) := (coherentTopology LightProfinite).yonedaEquiv <|
    (Adjunction.homEquiv (freeForgetAdjunction R) (S).toCondensed Y f)

  obtain ⟨T, π, hπ, x, hx⟩ := this S y

  let g : (free R).obj T.toCondensed ⟶ X :=
    ((freeForgetAdjunction R).homEquiv T.toCondensed X).symm
      ((coherentTopology LightProfinite).yonedaEquiv.symm x)

  have comm : g ≫ p = (lightProfiniteToLightCondSet ⋙ (LightCondensed.free R)).map π ≫ f := by
    symm
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_square_iff (freeForgetAdjunction R),
      Equiv.apply_symm_apply, Sheaf.hom_ext_iff,
      (coherentTopology LightProfinite).yonedaEquiv_symm_naturality_right, hx,
      (coherentTopology LightProfinite).map_yonedaEquiv',
      ← (coherentTopology LightProfinite).yonedaEquiv_symm_naturality_right]
    rfl
  exact ⟨T, π, g, (LightProfinite.epi_iff_surjective π).mpr hπ, comm⟩

instance : PreservesFiniteCoproducts (lightProfiniteToLightCondSet ⋙ (free R)) := by
  have : PreservesFiniteCoproducts lightProfiniteToLightCondSet :=
    LightProfinite.preservesFiniteCoproductsToLightCondSet
  have : IsLeftAdjoint (free R) := ⟨_, ⟨LightCondensed.freeForgetAdjunction R⟩⟩
  infer_instance

noncomputable def hc {S T : LightProfinite} (π : T ⟶ S) [Epi π]
    : IsColimit ((free R).mapCocone (explicitPullback.explicitRegular π)) := by
  have : IsLeftAdjoint (free R) := ⟨_, ⟨LightCondensed.freeForgetAdjunction R⟩⟩
  exact isColimitOfPreserves _ (explicitPullback.explicitRegularIsColimit _)

noncomputable def c {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ (S ⊗ ℕ∪{∞}))
    [Epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smart_cover π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (fibre ∞ (π ≫ snd _ _))) (σ : S ⟶ (fibre ∞ (π ≫ snd _ _)))
    (hr : fibre_incl ∞ (π ≫ snd _ _) ≫ r_inf = 𝟙 (fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (explicitPullback.fst π π))
      (lightProfiniteToLightCondSet.map (explicitPullback.snd π π))) ⋙ (free R)) where
  pt := X
  ι :=  by
    let ι_inf := fibre_incl ∞ (π ≫ snd _ _)
    let π_inf := (fibre_incl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _)

    let g_tilde : (lightProfiniteToLightCondSet ⋙ (free R)).obj T ⟶ X :=
      g - (lightProfiniteToLightCondSet ⋙ (free R)).map (r_inf ≫ ι_inf) ≫ g
          + (lightProfiniteToLightCondSet ⋙ (free R)).map (r_inf ≫ π_inf ≫ σ ≫ ι_inf) ≫ g
    refine parallelPairNatTrans (_ ≫ g_tilde) g_tilde ?_ (by rfl)

    rw [←cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map <| smart_cover π)]

    let hcc := isColimitOfHasBinaryCoproductOfPreservesColimit
      (lightProfiniteToLightCondSet ⋙ (free R)) T
      (explicitPullback (fibre_incl ∞ (π ≫ snd _ _) ≫ π) (fibre_incl ∞ (π ≫ snd _ _) ≫ π))

    apply hcc.hom_ext
    rintro (j | j)
    · simp only [const_obj_obj, Functor.comp_map, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, smart_cover, parallelPair_obj_zero,
        parallelPair_obj_one, parallelPair_map_left, parallelPair_map_right, const_obj_map,
        Category.comp_id]
      simp only [comp_obj, pair_obj_left, explicitPullback.diagonal, parallelPair_obj_zero,
        parallelPair_obj_one, ← map_comp_assoc, ← Functor.map_comp, coprod.desc_comp,
        colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
      erw [PullbackCone.IsLimit.lift_fst]
    · simp only [comp_obj, pair_obj_right, const_obj_obj, Functor.comp_map,
        BinaryCofan.mk_pt, BinaryCofan.ι_app_right, BinaryCofan.mk_inr,
        smart_cover, parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left,
        parallelPair_map_right, const_obj_map, Category.comp_id]
      simp only [←Functor.comp_map]
      simp only [←Category.assoc]
      simp only [←Functor.map_comp]
      rw [coprod.inr_desc]
      simp only [Preadditive.comp_add, Preadditive.comp_sub, g_tilde]
      simp only [Functor.comp_map, comp_obj, ← Category.assoc, ← Functor.map_comp]
      rw [explicitPullback.map_fst, explicitPullback.map_snd,
        Category.assoc _ (fibre_incl ∞ (π ≫ snd _ _)) r_inf, hr, Category.comp_id,
        Category.assoc _ (fibre_incl ∞ (π ≫ snd _ _)) r_inf, hr, Category.comp_id,
        sub_self, zero_add,
        sub_self, zero_add]
      unfold π_inf
      rw [← Category.assoc _ π _, ← Category.assoc _ (fibre_incl ∞ (π ≫ snd _ _) ≫ π) _,
        explicitPullback.condition]
      rfl

-- set_option maxHeartbeats 500000
private theorem proj_explicit {X Y : LightCondMod R} (p : X ⟶ Y) [hp : Epi p] {S : LightProfinite}
    (f : (free R).obj (S ⊗ ℕ∪{∞}).toCondensed ⟶ Y) :
      ∃ (S' : LightProfinite) (ψ : S' ⟶ S) (g : (free R).obj (S' ⊗ ℕ∪{∞}).toCondensed ⟶ X),
        Epi ψ ∧
          ((free R).map (lightProfiniteToLightCondSet.map
            (MonoidalCategoryStruct.tensorHom ψ (𝟙 ℕ∪{∞}))) ≫ f = g ≫ p) := by

  obtain ⟨T, π, g, hπ, comm⟩ := comm_sq R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ := refinedCover π

  use S', y'

  have : PreservesEpimorphisms (lightProfiniteToLightCondSet ⋙ (free R)) := by
    have : IsLeftAdjoint (free R) := (freeForgetAdjunction R).isLeftAdjoint
    infer_instance

  by_cases hS' : Nonempty S'
  -- The argument below only works if S' is non-empty. If S' is empty, the proof
  -- is easier anyway.
  · let hc : IsColimit ((free R).mapCocone (explicitPullback.explicitRegular π')) := hc R π'

    let ι_inf := fibre_incl ∞ (π' ≫ snd _ _)
    have : Mono ι_inf := fibre_incl_mono _ _
    have : Nonempty (fibre ∞ (π' ≫ snd _ _)) := by
      have : Epi (snd S' ℕ∪{∞}) := by
        apply prod_epi
      exact fibre_nonempty _ _

    have fibre_injective : Injective (fibre ∞ (π' ≫ snd _ _)) := injective_of_light _
    obtain ⟨r_inf, hr⟩ := fibre_injective.factors (𝟙 _) ι_inf

    simp only [ι_inf] at hr

    let π_inf := (fibre_incl ∞ (π' ≫ snd _ _) ≫ π' ≫ fst _ _)
    let σ := split.section_
    let hσ := split.id

    let gg := (lightProfiniteToLightCondSet ⋙ (free R)).map g' ≫ g

    let c' := c R π' gg r_inf σ hr

    have : fibre_incl ∞ (π' ≫ snd _ _) ≫ π' = fibre_incl ∞ (π' ≫ snd _ _) ≫ π' ≫ fst _ _ ≫
        lift (𝟙 _) (CompHausLike.ofHom _ (ContinuousMap.const S' (∞ : ℕ∪{∞}))) :=
      CartesianMonoidalCategory.hom_ext _ _ (by simp) (by ext; simp)

    have : c'.ι.app WalkingParallelPair.one ≫ p =
        (lightProfiniteToLightCondSet ⋙ (free R)).map
          (π' ≫ MonoidalCategoryStruct.tensorHom y' (𝟙 ℕ∪{∞})) ≫ f := by
      simp only [gg, comp_obj, parallelPair_obj_one, c, Functor.comp_map,
        const_obj_obj, Functor.map_comp, Category.assoc,
        Preadditive.comp_add, Preadditive.comp_sub, parallelPairNatTrans_app,
        Preadditive.add_comp, Preadditive.sub_comp, c']
      rw [comm]
      simp only [←Functor.map_comp, ←Functor.comp_map, ←Category.assoc, ←comp]
      simp only [Category.assoc]
      rw [sub_add, sub_eq_self, sub_eq_zero, ← Category.assoc _ π' _, this,
        ← Category.assoc _ (fst _ _), ← Category.assoc _ (π' ≫ fst _ _),
        ← Category.assoc σ, ← Category.assoc σ, hσ, Category.id_comp]
      rfl

    let desc_map : ((free R).obj (S' ⊗ ℕ∪{∞}).toCondensed) ⟶ X := hc.desc c'
    refine ⟨desc_map, inferInstance, ?_⟩

    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π'),
      ← Functor.comp_map, ←Functor.map_comp_assoc]
    change _ = (((free R).mapCocone (explicitPullback.explicitRegular π')).ι.app one ≫ hc.desc c') ≫ p
    erw [hc.fac]
    rw [this]
  · have : ¬Nonempty (S' ⊗ ℕ∪{∞} : LightProfinite) := empty_map hS' (fst _ _)
    have : IsIso π' := empty_iso this _
    obtain ⟨π'inv, h, _⟩ := this
    use (lightProfiniteToLightCondSet ⋙ (free R)).map (π'inv ≫ g') ≫ g
    refine ⟨hy', ?_⟩
    rw [←cancel_epi ((lightProfiniteToLightCondSet ⋙ (free R)).map π')]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [h, Category.id_comp]
    simp only [Category.assoc]
    rw [comm]
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [← comp]
    simp

theorem internallyProjective_ℕinfty : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R ℕ∪{∞}]
  intro X Y p hp S f
  obtain ⟨S', π, g, hπ, comm⟩ := proj_explicit R p f
  rw [LightProfinite.epi_iff_surjective] at hπ
  use S', π, hπ, g, comm

#print axioms internallyProjective_ℕinfty
