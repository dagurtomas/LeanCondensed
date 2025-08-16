import Mathlib
import LeanCondensed.Projects.Epi

open CategoryTheory Functor Opposite LightProfinite OnePoint Limits LightCondensed
  MonoidalCategory MonoidalClosed WalkingParallelPair WalkingParallelPairHom Topology

universe u

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

section

instance (x : X) : IsClosed {x} := isClosed_singleton

instance (S : Set Y) [IsClosed S] : IsClosed (f ⁻¹' S) := by
  exact IsClosed.preimage f.1.continuous inferInstance

instance : IsClosed (f ⁻¹' {y}) :=
  inferInstance

instance (S : Set X) [IsClosed S] : CompactSpace S := by
  exact isCompact_iff_compactSpace.mp (IsClosed.isCompact inferInstance)

instance : CompactSpace (f ⁻¹' {y}) := inferInstance

end

instance : TotallyDisconnectedSpace PUnit := by
  have := TotallySeparatedSpace.of_discrete
  apply TotallySeparatedSpace.totallyDisconnectedSpace

def fibre : LightProfinite :=
  ⟨
    TopCat.of (f ⁻¹' {y}),
    Subtype.totallyDisconnectedSpace,
    TopologicalSpace.Subtype.secondCountableTopology (f ⁻¹' {y})
  ⟩

def fibre_incl : fibre y f ⟶ X :=
  CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
def fibre_condition
  : fibre_incl y f ≫ f = (CompHausLike.ofHom _  <| ContinuousMap.const (fibre y f) y)
    := by ext x; exact x.2

lemma fibre_incl_mono : Mono (fibre_incl y f) := by
  rw [CompHausLike.mono_iff_injective]
  exact Subtype.val_injective

lemma fibre_incl_embedding : IsEmbedding (fibre_incl y f) := IsEmbedding.subtypeVal

lemma fibre_nonempty [hepi : Epi f] : Nonempty (fibre y f) := by
  rw [epi_iff_surjective f] at hepi
  obtain ⟨x, hx⟩ := hepi y
  exact ⟨x, hx⟩

def point : LightProfinite := LightProfinite.of PUnit

def fibreCone : PullbackCone (CompHausLike.ofHom _ <| ContinuousMap.const point y) f
    :=
  let space := f ⁻¹' {y}
  have : IsClosed space :=  IsClosed.preimage f.1.continuous isClosed_singleton
  have : IsCompact space := this.isCompact
  have : CompactSpace space := by
    exact isCompact_iff_compactSpace.mp this
  PullbackCone.mk (CompHausLike.ofHom _ <| ContinuousMap.const (fibre y f) PUnit.unit) (fibre_incl y f)
    (by ext x; simp only [fibre_incl, ConcreteCategory.comp_apply, CompHausLike.hom_ofHom,
      ContinuousMap.const_apply, ContinuousMap.coe_mk]; rw [x.2])

def fibreConeIsLimit : IsLimit (fibreCone y f) := by
  refine PullbackCone.IsLimit.mk (fibreCone _ _).condition ?_ ?_ ?_ ?_
  · intro cone
    have : ∀ z : cone.pt, f (cone.snd z) = y := by
      intro z
      rw [
        ←ConcreteCategory.comp_apply,
        ←cone.condition,
        ConcreteCategory.comp_apply
      ]
      rfl
    refine CompHausLike.ofHom _ <| ⟨fun z ↦ ⟨cone.snd z, this z⟩, ?_⟩
    rw [IsInducing.continuous_iff (fibre_incl_embedding y f).1]
    exact cone.snd.1.continuous
  repeat {exact fun cone ↦ rfl}
  · intro cone m hm hm'
    have := fibre_incl_mono y f
    erw [←cancel_mono (fibre_incl y f), hm']
    rfl

def fibreLift {Z : LightProfinite} (g : Z ⟶ X) (hg : ∀ z, f (g z) = y) : Z ⟶ fibre y f :=
  let space := f ⁻¹' {y}
  have : IsClosed space :=  IsClosed.preimage f.1.continuous isClosed_singleton
  have : IsCompact space := this.isCompact
  have : CompactSpace space := by
    exact isCompact_iff_compactSpace.mp this
  CompHausLike.ofHom _ <| ⟨fun z ↦ ⟨g z, hg z⟩, by rw [IsInducing.continuous_iff (fibre_incl_embedding y f).1]; exact g.1.continuous⟩

@[simp]
lemma fibreLift_comp {Z : LightProfinite} (g : Z ⟶ X) (hg : ∀ z, f (g z) = y)
  : fibreLift y f g hg ≫ fibre_incl y f = g := rfl

section

variable {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z)

instance : IsClosed {⟨x,y⟩ : X × Y | f x = g y} := by
  apply IsClosed.mk
  rw [isOpen_prod_iff]
  intro a b hab
  obtain ⟨u, v, hu, hv, ha, hb, huv⟩ := t2_separation hab
  refine ⟨
      f⁻¹'u, g⁻¹'v,
      f.1.continuous.isOpen_preimage _ hu,
      g.1.continuous.isOpen_preimage _ hv,
      ha, hb, ?_
  ⟩
  intro ⟨x, y⟩ ⟨hx, hy⟩ hxy
  simp only [Set.mem_preimage] at hx hy
  rw [hxy] at hx
  exact (Set.disjoint_iff (s := u) (t := v)).mp huv ⟨hx, hy⟩

instance : IsCompact {⟨x,y⟩ : X × Y | f x = g y} := by
  apply IsClosed.isCompact
  infer_instance

instance : CompactSpace {⟨x,y⟩ : X × Y | f x = g y} := by
  rw [←isCompact_iff_compactSpace]
  exact
    instIsCompactProdCarrierToTopAndTotallyDisconnectedSpaceSecondCountableTopologySetOfMatch_1PropEqCoeContinuousMapHomLightProfinite
      f g

end

def explicitPullback {X Y Z : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) : LightProfinite
    :=
  ⟨TopCat.of {⟨x,y⟩ : X × Y | f x = g y}, inferInstance, inferInstance⟩

namespace explicitPullback

variable {X Y Z : LightProfinite} {f : X ⟶ Z} {g : Y ⟶ Z}

def fst (f : X ⟶ Z) (g : Y ⟶ Z) : explicitPullback f g ⟶ X :=
  TopCat.ofHom
    ⟨
      (Prod.fst : X × Y → X) ∘ (Subtype.val : _ → X × Y),
      Continuous.comp continuous_fst continuous_subtype_val
    ⟩

def snd (f : X ⟶ Z) (g : Y ⟶ Z) : explicitPullback f g ⟶ Y :=
  TopCat.ofHom
    ⟨
      (Prod.snd : X × Y → Y) ∘ (Subtype.val : _ → X × Y),
      Continuous.comp continuous_snd continuous_subtype_val
    ⟩

instance epi_pullback [hepi : Epi f] : Epi (snd (f := f) (g := g)) := by
  rw [LightProfinite.epi_iff_surjective] at hepi ⊢
  intro y
  obtain ⟨x, hx⟩ := hepi (g y)
  exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩


lemma condition : fst (f := f) (g := g) ≫ f = snd (f := f) (g := g) ≫ g := by
  ext ⟨_,hxy⟩
  exact hxy

def Cone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (fst _ _) (snd _ _) condition

lemma Cone.fst_eq : (Cone f g).fst = fst _ _ := rfl
lemma Cone.snd_eq : (Cone f g).snd = snd _ _ := rfl

def IsLimit : IsLimit (Cone f g) := by
  let space := {⟨x,y⟩ : X × Y | f x = g y}
  have : IsClosed space := by
    apply IsClosed.mk
    rw [isOpen_prod_iff]
    intro a b hab
    obtain ⟨u, v, hu, hv, ha, hb, huv⟩ := t2_separation hab
    refine ⟨
      f⁻¹'u, g⁻¹'v,
      f.1.continuous.isOpen_preimage _ hu,
      g.1.continuous.isOpen_preimage _ hv,
      ha, hb, ?_
    ⟩
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [Set.mem_preimage] at hx hy
    intro hxy
    rw [hxy] at hx
    exact (Set.disjoint_iff (s := u) (t := v)).mp huv ⟨hx, hy⟩
  have : IsCompact space := this.isCompact
  have : CompactSpace space := by
    exact isCompact_iff_compactSpace.mp this

  refine PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_
  · intro cone
    have : ∀ z, ⟨cone.fst z, cone.snd z⟩ ∈ space := by
      intro z
      simp only [Set.mem_setOf_eq, space]
      rw [←ConcreteCategory.comp_apply, cone.condition]
      rfl
    refine TopCat.ofHom ⟨fun z ↦ ⟨⟨cone.fst z, cone.snd z⟩, this z⟩, ?_⟩
    rw [(IsInducing.continuous_iff IsEmbedding.subtypeVal.1)]
    exact Continuous.prodMk cone.fst.1.continuous cone.snd.1.continuous
  repeat {intro cone; ext z; rfl}
  · intro cone m hm hm'
    ext z
    apply Subtype.ext
    apply Prod.ext
    change fst _ _ (↑((ConcreteCategory.hom m) z)) = _
    rw [←ConcreteCategory.comp_apply, hm]
    rfl
    change snd _ _ (↑((ConcreteCategory.hom m) z)) = _
    rw [←ConcreteCategory.comp_apply, hm']
    rfl

def diagonal (f : X ⟶ Y) : X ⟶ explicitPullback f f
  := PullbackCone.IsLimit.lift IsLimit (𝟙 _) (𝟙 _) rfl

def map {X' Y' Z' : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z')
  (g' : Y' ⟶ Z') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
  (eq₁ : f ≫ i₃ = i₁ ≫ f') (eq₂ : g ≫ i₃ = i₂ ≫ g')
  : explicitPullback f g ⟶ explicitPullback f' g' :=
    PullbackCone.IsLimit.lift IsLimit (fst _ _ ≫ i₁) (snd _ _ ≫ i₂)
      (by rw [Category.assoc, Category.assoc, ←eq₁, ←eq₂, ←Cone.fst_eq,
              PullbackCone.condition_assoc, Cone.snd_eq])

lemma map_fst {X' Y' Z' : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z')
  (g' : Y' ⟶ Z') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
  (eq₁ : f ≫ i₃ = i₁ ≫ f') (eq₂ : g ≫ i₃ = i₂ ≫ g') : map f g f' g' i₁ i₂ i₃ eq₁ eq₂ ≫ fst f' g' = fst f g ≫ i₁ := rfl

lemma map_snd {X' Y' Z' : LightProfinite} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z')
  (g' : Y' ⟶ Z') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z')
  (eq₁ : f ≫ i₃ = i₁ ≫ f') (eq₂ : g ≫ i₃ = i₂ ≫ g') : map f g f' g' i₁ i₂ i₃ eq₁ eq₂ ≫ snd f' g' = snd f g ≫ i₂ := rfl

def explicitPair  {X Y : LightProfinite} (π : X ⟶ Y) : WalkingParallelPair ⥤ LightCondSet
  := parallelPair
    (lightProfiniteToLightCondSet.map (fst π π)) (lightProfiniteToLightCondSet.map (snd π π))

noncomputable def explicitPullbackIsoPullback {X Y : LightProfinite} (π : X ⟶ Y) : explicitPullback π π ≅ pullback π π :=
  Limits.IsLimit.conePointUniqueUpToIso (IsLimit (f := π) (g := π)) (pullback.isLimit π π)

noncomputable def explicitPairIsoPair {X Y : LightProfinite} (π : X ⟶ Y) : explicitPair π ≅ πpair π :=
  parallelPair.ext
    (lightProfiniteToLightCondSet.mapIso (explicitPullbackIsoPullback π) : (explicitPair π).obj zero ≅ (πpair π).obj zero)
    (Iso.refl _)
    (
        by simp [←Functor.map_comp, explicitPair, πpair, explicitPullbackIsoPullback]; rfl
    )
    (
        by simp [←Functor.map_comp, explicitPair, πpair, explicitPullbackIsoPullback]; rfl
    )

def explicitRegular {X Y : LightProfinite} (π : X ⟶ Y)
    : Cofork (lightProfiniteToLightCondSet.map <| fst π π)
      (lightProfiniteToLightCondSet.map <| snd π π) :=
  Cofork.ofπ (lightProfiniteToLightCondSet.map π)
    (by simp only [←Functor.map_comp, condition])

noncomputable def explicitRegularIsColimit {X Y : LightProfinite} (π : X ⟶ Y) [hepi : Epi π]
    : IsColimit (explicitRegular π) := by
  rw [LightProfinite.epi_iff_surjective, ←LightProfinite.effectiveEpi_iff_surjective] at hepi
  exact (
    IsColimit.equivOfNatIsoOfIso
      (explicitPairIsoPair _)
      _
      (regular _)
      (Cofork.ext (Iso.refl _) rfl)
  ).symm (regular_IsColimit _)
