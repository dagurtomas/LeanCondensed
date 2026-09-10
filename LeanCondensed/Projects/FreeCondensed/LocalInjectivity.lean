module

public import LeanCondensed.Projects.FreeCondensed.TopologicalFree

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- A single effective epimorphism lying in an equalizer sieve gives a coherent covering of that
sieve.  This is the site-theoretic target for the finite closed-cover part of local injectivity. -/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpi
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U V : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (π : V ⟶ U) [EffectiveEpi π]
    (hπ : F.map π.op x = F.map π.op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  refine ⟨Unit, inferInstance, (fun _ => V), (fun _ => π), ?_, ?_⟩
  · simpa [CategoryTheory.effectiveEpi_iff_effectiveEpiFamily] using (inferInstance : EffectiveEpi π)
  · intro _
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ

/-- A closed subset of a light profinite space, with the induced topology, is light profinite. -/
noncomputable def closedSubLightProfinite {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    LightProfinite.{0} :=
  @LightProfinite.of s inferInstance (isCompact_iff_compactSpace.mp hs.isCompact)
    inferInstance inferInstance inferInstance

/-- The inclusion of a closed light-profinite subspace. -/
noncomputable def closedSubLightProfiniteι {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s) :
    closedSubLightProfinite s hs ⟶ X := by
  let _ : CompactSpace s := isCompact_iff_compactSpace.mp hs.isCompact
  exact CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
lemma closedSubLightProfiniteι_apply {X : LightProfinite.{0}} (s : Set X) (hs : IsClosed s)
    (x : closedSubLightProfinite s hs) : closedSubLightProfiniteι s hs x = (x : s).1 := rfl

/-- A finite jointly-surjective family in `LightProfinite` is an effective-epi family. -/
lemma effectiveEpiFamily_of_jointly_surjective {α : Type} [Finite α]
    {B : LightProfinite.{0}} (X : α → LightProfinite.{0}) (π : (a : α) → X a ⟶ B)
    (hπ : ∀ b : B, ∃ a, ∃ x : X a, π a x = b) : EffectiveEpiFamily X π := by
  rw [← CategoryTheory.effectiveEpi_desc_iff_effectiveEpiFamily]
  rw [LightProfinite.effectiveEpi_iff_surjective]
  intro b
  obtain ⟨a, x, hx⟩ := hπ b
  refine ⟨Sigma.ι X a x, ?_⟩
  exact (ConcreteCategory.congr_hom (Sigma.ι_desc π a) x).trans hx

/-- A finite effective-epi family lying in an equalizer sieve gives a coherent covering of that
sieve. -/
lemma freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (V : α → LightProfinite.{0}) (π : (a : α) → V a ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ a, F.map (π a).op x = F.map (π a).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun a => by
    simpa [CategoryTheory.Presheaf.equalizerSieve] using hπ a⟩

/-- A finite effective-epi family with local preimages gives a coherent covering of the image
sieve. -/
lemma presheaf_imageSieve_mem_of_effectiveEpiFamily
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    [EffectiveEpiFamily V π]
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
  exact ⟨α, inferInstance, V, π, inferInstance, fun i => by
    simpa [CategoryTheory.Presheaf.imageSieve] using hπ i⟩

/-- A finite jointly-surjective family with local preimages gives a coherent covering of the image
sieve. -/
lemma presheaf_imageSieve_mem_of_finite_jointly_surjective
    {α : Type} [Finite α]
    {F G : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (φ : F ⟶ G) (s : G.obj ⟨U⟩)
    (V : α → LightProfinite.{0}) (π : (i : α) → V i ⟶ U)
    (hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u)
    (hπ : ∀ i, ∃ t : F.obj ⟨V i⟩,
      φ.app ⟨V i⟩ t = G.map (π i).op s) :
    CategoryTheory.Presheaf.imageSieve φ s ∈ (coherentTopology LightProfinite) U := by
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact presheaf_imageSieve_mem_of_effectiveEpiFamily φ s V π hπ

/-- A finite closed cover whose inclusions lie in an equalizer sieve gives a coherent covering of
that sieve.  This packages the closed-cover replacement for the tempting but invalid clopen
refinement. -/
lemma freePresheaf_equalizerSieve_mem_of_finite_closed_cover
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ} {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩) (C : α → Set U) (hC : ∀ a, IsClosed (C a))
    (hcover : ∀ u : U, ∃ a, u ∈ C a)
    (hπ : ∀ a, F.map (closedSubLightProfiniteι (C a) (hC a)).op x =
      F.map (closedSubLightProfiniteι (C a) (hC a)).op y) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈ (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun a => closedSubLightProfinite (C a) (hC a)
  let π : (a : α) → V a ⟶ U := fun a => closedSubLightProfiniteι (C a) (hC a)
  have hsurj : ∀ u : U, ∃ a, ∃ x : V a, π a x = u := by
    intro u
    obtain ⟨a, hu⟩ := hcover u
    refine ⟨a, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C a) (hC a) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  exact freePresheaf_equalizerSieve_mem_of_effectiveEpiFamily x y V π hπ

/-- Pulling back a presheaf equalizer sieve restricts the two sections along the same arrow. -/
lemma _root_.CategoryTheory.Presheaf.equalizerSieve_pullback_eq
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U V : LightProfinite.{0}} (π : V ⟶ U)
    (x y : F.obj ⟨U⟩) :
    (CategoryTheory.Presheaf.equalizerSieve x y).pullback π =
      CategoryTheory.Presheaf.equalizerSieve (F.map π.op x) (F.map π.op y) := by
  ext W f
  simp [CategoryTheory.Presheaf.equalizerSieve]

/-- If the equalizer sieve is covering locally on every member of a finite closed cover, then it is
covering on the original space.  This is the transitivity form of the closed-cover reduction. -/
lemma presheaf_equalizerSieve_mem_of_finite_closed_cover_locally
    {α : Type} [Finite α]
    {F : LightProfiniteᵒᵖ ⥤ ModuleCat.{0} ℤ}
    {U : LightProfinite.{0}}
    (x y : F.obj ⟨U⟩)
    (C : α → Set U) (hC : ∀ i, IsClosed (C i))
    (hcover : ∀ u : U, ∃ i, u ∈ C i)
    (hlocal : ∀ i,
      CategoryTheory.Presheaf.equalizerSieve
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op x)
        (F.map (closedSubLightProfiniteι (C i) (hC i)).op y) ∈
          (coherentTopology LightProfinite)
            (closedSubLightProfinite (C i) (hC i))) :
    CategoryTheory.Presheaf.equalizerSieve x y ∈
      (coherentTopology LightProfinite) U := by
  let V : α → LightProfinite := fun i => closedSubLightProfinite (C i) (hC i)
  let π : (i : α) → V i ⟶ U := fun i => closedSubLightProfiniteι (C i) (hC i)
  have hsurj : ∀ u : U, ∃ i, ∃ v : V i, π i v = u := by
    intro u
    obtain ⟨i, hu⟩ := hcover u
    refine ⟨i, ⟨u, hu⟩, ?_⟩
    exact closedSubLightProfiniteι_apply (C i) (hC i) ⟨u, hu⟩
  haveI : EffectiveEpiFamily V π := effectiveEpiFamily_of_jointly_surjective V π hsurj
  let S₀ : Sieve U := Sieve.ofArrows V π
  have hS₀ : S₀ ∈ (coherentTopology LightProfinite) U := by
    apply CategoryTheory.coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    exact ⟨α, inferInstance, V, π, inferInstance, fun i => Sieve.ofArrows_mk V π i⟩
  refine (coherentTopology LightProfinite).transitive hS₀
    (CategoryTheory.Presheaf.equalizerSieve x y) ?_
  intro Y f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff V π f).mp hf
  have hπ : (CategoryTheory.Presheaf.equalizerSieve x y).pullback (π i) ∈
      (coherentTopology LightProfinite) (V i) := by
    simpa [S₀, V, π, CategoryTheory.Presheaf.equalizerSieve_pullback_eq] using hlocal i
  simpa [Sieve.pullback_comp] using
    ((coherentTopology LightProfinite).pullback_stable g hπ)

/-- Equality-pattern loci cut out by finitely many equalities between maps to a light profinite
space are closed.  The second TFC3 round uses these as closed members of a coherent cover; the
remaining coefficient extraction happens after restricting the free presheaf to these loci. -/
lemma finiteMapEqualityPattern_isClosed {α : Type} [Finite α] {U S : LightProfinite.{0}}
    (f : α → (U ⟶ S)) (r : α → α → Prop) :
    IsClosed {u : U | ∀ i j, r i j → (f i) u = (f j) u} := by
  classical
  rw [show {u : U | ∀ i j, r i j → (f i) u = (f j) u} =
      ⋂ i, ⋂ j, ⋂ _h : r i j, {u : U | (f i) u = (f j) u} by
    ext u
    simp]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (f i).hom.hom.continuous (f j).hom.hom.continuous

/-- If `f` is injective on the union of the supports of two finitely supported functions, equality
after `Finsupp.mapDomain f` reflects equality. -/
lemma finsupp_mapDomain_eq_of_eq_of_injOn_support_union {α β : Type*} [DecidableEq α]
    [DecidableEq β] (f : α → β) {a b : α →₀ ℤ}
    (hinj : Set.InjOn f ((↑((a.support : Finset α) ∪ b.support) : Set α)))
    (h : Finsupp.mapDomain f a = Finsupp.mapDomain f b) : a = b := by
  ext x
  by_cases hx : x ∈ (a.support : Finset α) ∪ b.support
  · have ha : (Finsupp.mapDomain f a) (f x) = a x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_left _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : a x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    have hb : (Finsupp.mapDomain f b) (f x) = b x := by
      rw [Finsupp.mapDomain_apply_eq_sum]
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hy hyx
        rw [Finset.mem_filter] at hy
        exact (hyx (hinj (by exact Finset.mem_coe.mpr (Finset.mem_union_right _ hy.1))
          (by exact Finset.mem_coe.mpr hx) hy.2)).elim
      · intro hxnot
        have : b x = 0 := by
          by_contra hne
          exact hxnot (by
            rw [Finset.mem_filter]
            exact ⟨(Finsupp.mem_support_iff).mpr hne, rfl⟩)
        simp [this]
    exact ha ▸ hb ▸ DFunLike.congr_fun h (f x)
  · have hxa : x ∉ a.support := fun hxa => hx (Finset.mem_union_left _ hxa)
    have hxb : x ∉ b.support := fun hxb => hx (Finset.mem_union_right _ hxb)
    have hax : a x = 0 := by
      by_contra hne
      exact hxa ((Finsupp.mem_support_iff).mpr hne)
    have hbx : b x = 0 := by
      by_contra hne
      exact hxb ((Finsupp.mem_support_iff).mpr hne)
    simp [hax, hbx]

/-- If a finitely supported integer combination vanishes after `mapDomain`, then every support
point collides under the domain map with another support point. -/
lemma finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (c : α →₀ ℤ) {x : α} (hx : x ∈ c.support)
    (f : α → β) (hzero : Finsupp.mapDomain f c = 0) :
    ∃ y, y ∈ c.support ∧ y ≠ x ∧ f y = f x := by
  by_contra hnone
  have hsum : (Finsupp.mapDomain f c) (f x) = c x := by
    rw [Finsupp.mapDomain_apply_eq_sum]
    refine Finset.sum_eq_single x ?_ ?_
    · intro y hy hyx
      rw [Finset.mem_filter] at hy
      exact (hnone ⟨y, hy.1, hyx, hy.2⟩).elim
    · intro hxnot
      exact (hxnot (by
        rw [Finset.mem_filter]
        exact ⟨hx, rfl⟩)).elim
  have hzero_apply : (Finsupp.mapDomain f c) (f x) = 0 := by
    rw [hzero]
    rfl
  rw [hsum] at hzero_apply
  exact (Finsupp.mem_support_iff.mp hx) hzero_apply

/-- If two distinct support points collide under the domain map, then the support of the
`mapDomain` result has strictly smaller cardinality.  This only uses the upper bound by the image
of the original support, so cancellations after `mapDomain` are allowed. -/
lemma finsupp_mapDomain_support_card_lt_of_pair_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (c : α →₀ ℤ)
    {x y : α} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hne : x ≠ y) (hxy : f x = f y) :
    (Finsupp.mapDomain f c).support.card < c.support.card := by
  have hsubset : (Finsupp.mapDomain f c).support ⊆ c.support.image f := by
    exact Finsupp.mapDomain_support
  have hcard_support : (Finsupp.mapDomain f c).support.card ≤ (c.support.image f).card :=
    Finset.card_le_card hsubset
  have hnotinj : ¬ Set.InjOn f (c.support : Set α) := by
    intro hinj
    exact hne (hinj (by exact Finset.mem_coe.mpr hx) (by exact Finset.mem_coe.mpr hy) hxy)
  have hcard_image_lt : (c.support.image f).card < c.support.card := by
    have hle : (c.support.image f).card ≤ c.support.card := Finset.card_image_le
    have hnecard : (c.support.image f).card ≠ c.support.card := by
      intro heq
      exact hnotinj ((Finset.card_image_iff (s := c.support) (f := f)).mp heq)
    exact Nat.lt_of_le_of_ne hle hnecard
  exact lt_of_le_of_lt hcard_support hcard_image_lt

lemma freePresheaf_map_sub
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (a b : (freePresheaf S).obj ⟨U⟩) :
    (freePresheaf S).map π.op (a - b) =
      (freePresheaf S).map π.op a - (freePresheaf S).map π.op b := by
  exact ((freePresheaf S).map π.op).hom.map_sub a b

lemma freePresheaf_restrict_support_card_lt_of_eq_on_pair
    (S : LightProfinite.{0}) {U V : LightProfinite.{0}} (π : V ⟶ U)
    (c : (freePresheaf S).obj ⟨U⟩)
    {g h : U ⟶ S} (hg : g ∈ c.support) (hh : h ∈ c.support)
    (hne : g ≠ h) (heq : π ≫ g = π ≫ h) :
    (((freePresheaf S).map π.op c).support.card < c.support.card) := by
  classical
  change (Finsupp.mapDomain (fun g : U ⟶ S => π ≫ g) c).support.card < c.support.card
  exact finsupp_mapDomain_support_card_lt_of_pair_eq (fun g : U ⟶ S => π ≫ g) c hg hh hne heq

lemma freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero
    (S U : LightProfinite.{0}) {a b : (freePresheaf S).obj ⟨U⟩}
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b)
    (u : U) :
    Finsupp.mapDomain (fun g : U ⟶ S => g u) (a - b) = 0 := by
  classical
  let f : S.toCondensed.obj.obj ⟨U⟩ → S :=
    fun g => ((show U ⟶ S from g) u)
  change Finsupp.mapDomain f (a - b) = 0
  have hpoint : Finsupp.mapDomain f a = Finsupp.mapDomain f b := by
    simpa [f] using freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq S U h u
  calc
    Finsupp.mapDomain f (a - b) = Finsupp.mapDomain f a - Finsupp.mapDomain f b := by
      exact Finsupp.mapDomain_sub
    _ = 0 := by simp [hpoint]

/-- Indices for the one-step collision cover: support maps distinct from the chosen `g₀`. -/
def freePresheaf_collisionCoverIndex
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) : Type :=
  {g : S.toCondensed.obj.obj ⟨U⟩ // g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}

instance freePresheaf_collisionCoverIndex_finite
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    Finite (freePresheaf_collisionCoverIndex S U c g₀) := by
  classical
  let collisionSet : Set (S.toCondensed.obj.obj ⟨U⟩) :=
    {g | g ∈ c.support ∧ (show U ⟶ S from g) ≠ g₀}
  have hfinite : collisionSet.Finite := by
    refine Set.Finite.ofFinset
      (c.support.filter fun g => (show U ⟶ S from g) ≠ g₀) ?_
    intro g
    simp [collisionSet]
  change Finite collisionSet
  exact hfinite.to_subtype

/-- The closed equality locus for a collision-cover index. -/
noncomputable def freePresheaf_collisionCoverSet
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    freePresheaf_collisionCoverIndex S U c g₀ → Set U :=
  fun g => {u | (show U ⟶ S from g.1) u = g₀ u}

lemma freePresheaf_collisionCover_isClosed
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    (g₀ : U ⟶ S) :
    ∀ i, IsClosed (freePresheaf_collisionCoverSet S U c g₀ i) := by
  intro i
  exact isClosed_eq (show U ⟶ S from i.1).hom.hom.continuous g₀.hom.hom.continuous

lemma freePresheaf_collisionCover_covers_of_pointwise_zero
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (hzero : ∀ u : U,
      Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0) :
    ∀ u : U, ∃ i, u ∈ freePresheaf_collisionCoverSet S U c g₀ i := by
  classical
  intro u
  obtain ⟨g, hg, hne, heq⟩ :=
    finsupp_exists_ne_mem_support_apply_eq_of_mapDomain_eq_zero c hg₀
      (fun g : U ⟶ S => g u) (hzero u)
  exact ⟨⟨g, hg, hne⟩, heq⟩

lemma freePresheaf_collisionCover_restrict_card_lt
    (S U : LightProfinite.{0}) (c : (freePresheaf S).obj ⟨U⟩)
    {g₀ : U ⟶ S} (hg₀ : g₀ ∈ c.support)
    (i : freePresheaf_collisionCoverIndex S U c g₀) :
    let C := freePresheaf_collisionCoverSet S U c g₀ i
    let hC := freePresheaf_collisionCover_isClosed S U c g₀ i
    (((freePresheaf S).map (closedSubLightProfiniteι C hC).op c).support.card <
      c.support.card) := by
  classical
  dsimp only
  apply freePresheaf_restrict_support_card_lt_of_eq_on_pair S
    (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
      (freePresheaf_collisionCover_isClosed S U c g₀ i)) c i.2.1 hg₀ i.2.2
  ext x
  change (show U ⟶ S from i.1)
      (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x) =
    g₀ (closedSubLightProfiniteι (freePresheaf_collisionCoverSet S U c g₀ i)
        (freePresheaf_collisionCover_isClosed S U c g₀ i) x)
  rw [closedSubLightProfiniteι_apply]
  exact (x : freePresheaf_collisionCoverSet S U c g₀ i).2

lemma freePresheafToTopologicalFreePresheaf_equalizerSieve_mem
    (S U : LightProfinite.{0})
    (a b : (freePresheaf S).obj ⟨U⟩)
    (h : (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b) :
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U := by
  classical
  let P : ℕ → Prop := fun n => ∀ (U : LightProfinite.{0})
      (a b : (freePresheaf S).obj ⟨U⟩),
    (a - b).support.card = n →
    (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ a =
      (freePresheafToTopologicalFreePresheaf S).app ⟨U⟩ b →
    CategoryTheory.Presheaf.equalizerSieve a b ∈
      (coherentTopology LightProfinite) U
  have hind : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U a b hcard h
      by_cases hn : n = 0
      · have hcard0 : (a - b).support.card = 0 := hcard.trans hn
        have hempty : (a - b).support = ∅ := Finset.card_eq_zero.mp hcard0
        have hsub : a - b = 0 := Finsupp.support_eq_empty.mp hempty
        have hab : a = b := sub_eq_zero.mp hsub
        subst b
        rw [CategoryTheory.Presheaf.equalizerSieve_self_eq_top]
        exact (coherentTopology LightProfinite).top_mem U
      · have hcard_ne : (a - b).support.card ≠ 0 := by
          intro hzero
          exact hn (hcard.symm.trans hzero)
        obtain ⟨g₀, hg₀⟩ :=
          (Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne) : (a - b).support.Nonempty)
        let c : (freePresheaf S).obj ⟨U⟩ := a - b
        have hg₀c : g₀ ∈ c.support := by
          change g₀ ∈ (a - b).support
          exact hg₀
        let I := freePresheaf_collisionCoverIndex S U c g₀
        haveI : Finite I := freePresheaf_collisionCoverIndex_finite S U c g₀
        let C : I → Set U := freePresheaf_collisionCoverSet S U c g₀
        let hC : ∀ i, IsClosed (C i) := freePresheaf_collisionCover_isClosed S U c g₀
        have hzero : ∀ u : U, Finsupp.mapDomain (fun g : U ⟶ S => g u) c = 0 := by
          intro u
          simpa [c] using
            freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_sub_eq_zero S U h u
        have hcover : ∀ u : U, ∃ i, u ∈ C i := by
          simpa [c, C] using
            freePresheaf_collisionCover_covers_of_pointwise_zero S U c hg₀c hzero
        refine presheaf_equalizerSieve_mem_of_finite_closed_cover_locally a b C hC hcover ?_
        intro i
        let V : LightProfinite.{0} := closedSubLightProfinite (C i) (hC i)
        let π : V ⟶ U := closedSubLightProfiniteι (C i) (hC i)
        let aV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op a
        let bV : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op b
        have hres : (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ aV =
            (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ bV := by
          exact (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op a).trans
            ((congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
              (topologicalFreePresheaf S).map π.op z) h).trans
            (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op b).symm)
        have hdropc : (((freePresheaf S).map π.op c).support.card < c.support.card) := by
          simpa [c, I, C, hC, V, π] using
            freePresheaf_collisionCover_restrict_card_lt S U c hg₀c i
        have hmap_sub : (freePresheaf S).map π.op c = aV - bV := by
          exact freePresheaf_map_sub S π a b
        have hdrop : (aV - bV).support.card < n := by
          calc
            (aV - bV).support.card = ((freePresheaf S).map π.op c).support.card := by
              rw [← hmap_sub]
            _ < c.support.card := hdropc
            _ = n := by simpa [c] using hcard
        exact ih (aV - bV).support.card hdrop V aV bV rfl hres
  exact hind (a - b).support.card U a b rfl h

instance freePresheafToTopologicalFreePresheaf_isLocallyInjective
    (S : LightProfinite.{0}) :
    CategoryTheory.Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  refine ⟨?_⟩
  intro Uop a b h
  rcases Uop with ⟨U⟩
  change CategoryTheory.Presheaf.equalizerSieve a b ∈ (coherentTopology LightProfinite) U
  exact freePresheafToTopologicalFreePresheaf_equalizerSieve_mem S U a b h

/-- For a finite target, the presheaf comparison is locally injective.  The covering pieces are the
closed loci on which every support map of the two sections is constant. -/
instance freePresheafToTopologicalFreePresheaf_isLocallyInjective_of_finite
    (S : LightProfinite.{0}) [Finite S] :
    CategoryTheory.Presheaf.IsLocallyInjective (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) := by
  classical
  refine ⟨?_⟩
  intro Uop a b h
  rcases Uop with ⟨U⟩
  change CategoryTheory.Presheaf.equalizerSieve a b ∈ (coherentTopology LightProfinite) U
  let supp : Finset (U ⟶ S) := (a.support : Finset (U ⟶ S)) ∪ b.support
  let α := { c : supp → S // ∃ u : U, ∀ g : supp, (g : U ⟶ S) u = c g }
  haveI : Finite α := by dsimp [α]; infer_instance
  let C : α → Set U := fun c => {u : U | ∀ g : supp, (g : U ⟶ S) u = c.1 g}
  have hC : ∀ c, IsClosed (C c) := by
    intro c
    rw [show C c = ⋂ g : supp, {u : U | (g : U ⟶ S) u = c.1 g} by
      ext u
      simp [C]]
    exact isClosed_iInter fun g => isClosed_eq (g : U ⟶ S).hom.hom.continuous continuous_const
  have hcover : ∀ u : U, ∃ c, u ∈ C c := by
    intro u
    refine ⟨⟨fun g : supp => (g : U ⟶ S) u, ⟨u, fun g => rfl⟩⟩, ?_⟩
    intro g
    rfl
  apply freePresheaf_equalizerSieve_mem_of_finite_closed_cover a b C hC hcover
  intro c
  let V : LightProfinite.{0} := closedSubLightProfinite (C c) (hC c)
  let π : V ⟶ U := closedSubLightProfiniteι (C c) (hC c)
  let a' : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op a
  let b' : (freePresheaf S).obj ⟨V⟩ := (freePresheaf S).map π.op b
  change a' = b'
  obtain ⟨u0, hu0⟩ := c.2
  let v0 : V := ⟨u0, hu0⟩
  have hres : (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ a' =
      (freePresheafToTopologicalFreePresheaf S).app ⟨V⟩ b' := by
    exact (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op a).trans
      ((congrArg (fun z : (topologicalFreePresheaf S).obj ⟨U⟩ =>
        (topologicalFreePresheaf S).map π.op z) h).trans
      (freePresheafToTopologicalFreePresheaf_naturality_apply S π.op b).symm)
  have hpoint := freePresheafToTopologicalFreePresheaf_pointwise_mapDomain_eq_of_eq S V hres v0
  apply finsupp_mapDomain_eq_of_eq_of_injOn_support_union
    (fun r : V ⟶ S => r v0) ?_ hpoint
  intro r hr t ht hrt
  have hconst : ∀ q : S.toCondensed.obj.obj ⟨V⟩,
      q ∈ a'.support ∪ b'.support → ∀ x y : V,
        (show V ⟶ S from q) x = (show V ⟶ S from q) y := by
    intro q hq x y
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · have himg : q ∈ Finset.image (fun g : U ⟶ S => π ≫ g) a.support :=
        Finsupp.mapDomain_support hq
      obtain ⟨g, hg, hgq⟩ := Finset.mem_image.mp himg
      have hgq' : π ≫ g = q := hgq
      have hxs : g (π x) = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := by
        have hxmem : (π x) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) x ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (x : C c).2
        exact hxmem ⟨g, Finset.mem_union_left b.support hg⟩
      have hys : g (π y) = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := by
        have hymem : (π y) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) y ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (y : C c).2
        exact hymem ⟨g, Finset.mem_union_left b.support hg⟩
      calc
        (show V ⟶ S from q) x = g (π x) := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' x).symm
        _ = c.1 ⟨g, Finset.mem_union_left b.support hg⟩ := hxs
        _ = g (π y) := hys.symm
        _ = (show V ⟶ S from q) y := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' y)
    · have himg : q ∈ Finset.image (fun g : U ⟶ S => π ≫ g) b.support :=
        Finsupp.mapDomain_support hq
      obtain ⟨g, hg, hgq⟩ := Finset.mem_image.mp himg
      have hgq' : π ≫ g = q := hgq
      have hxs : g (π x) = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := by
        have hxmem : (π x) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) x ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (x : C c).2
        exact hxmem ⟨g, Finset.mem_union_right a.support hg⟩
      have hys : g (π y) = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := by
        have hymem : (π y) ∈ C c := by
          change closedSubLightProfiniteι (C c) (hC c) y ∈ C c
          rw [closedSubLightProfiniteι_apply]
          exact (y : C c).2
        exact hymem ⟨g, Finset.mem_union_right a.support hg⟩
      calc
        (show V ⟶ S from q) x = g (π x) := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' x).symm
        _ = c.1 ⟨g, Finset.mem_union_right a.support hg⟩ := hxs
        _ = g (π y) := hys.symm
        _ = (show V ⟶ S from q) y := by
          simpa [CategoryTheory.comp_apply] using (ConcreteCategory.congr_hom hgq' y)
  ext x
  have hr' : r ∈ (a'.support : Finset (V ⟶ S)) ∪ b'.support := Finset.mem_coe.mp hr
  have ht' : t ∈ (a'.support : Finset (V ⟶ S)) ∪ b'.support := Finset.mem_coe.mp ht
  calc
    r x = r v0 := hconst r hr' x v0
    _ = t v0 := hrt
    _ = t x := (hconst t ht' x v0).symm

end LightCondAb
