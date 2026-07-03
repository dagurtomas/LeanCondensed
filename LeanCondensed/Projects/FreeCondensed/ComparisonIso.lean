module

public import LeanCondensed.Projects.FreeCondensed.LocalSurjectivity

@[expose] public section

noncomputable section

open CategoryTheory LightCondensed LightCondSet LightCondAb Limits
open scoped BigOperators BoundedContinuousFunction

namespace LightCondAb

variable (S : LightProfinite.{0})

/-- Evaluation on topological free abelian groups is natural in the light profinite source. -/
lemma topologicalFreeEval_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeMap f ≫ topologicalFreeEval T g =
      topologicalFreeEval S (g.comap f.hom.hom) := by
  ext μ
  let L : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeMap f ≫ topologicalFreeEval T g).hom.toLinearMap
  let R : (topologicalFree S) →ₗ[ℤ] ℤ :=
    (topologicalFreeEval S (g.comap f.hom.hom)).hom.toLinearMap
  change L μ = R μ
  suffices L = R by rw [this]
  refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
  change (topologicalFreeEval T g).hom ((topologicalFreeMap f).hom (Finsupp.single s (1 : ℤ))) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom (Finsupp.single s (1 : ℤ))
  rw [topologicalFreeMap_single, topologicalFreeEval_single, topologicalFreeEval_single]
  rfl

/-- The induced morphism between represented light condensed abelian groups. -/
noncomputable def topologicalFreeEvalCondensed (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      LightCondensed.topModuleToLightCondAbObj discreteIntTopModule :=
  LightCondensed.topModuleToLightCondAbMap (topologicalFreeEval S f)

/-- The induced morphism from the represented topological free abelian group to the discrete
light condensed abelian group `ℤ`. -/
noncomputable def topologicalFreeEvalDiscrete (f : LocallyConstant S ℤ) :
    topologicalFreeCondensed S ⟶
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom

/-- Represented topological-free evaluation is natural in the light profinite source. -/
lemma topologicalFreeEvalCondensed_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g =
      topologicalFreeEvalCondensed S (g.comap f.hom.hom) := by
  ext U h
  change (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeCondensedMap f ≫ topologicalFreeEvalCondensed T g).hom.app U h) =
    (show C(↑U.unop.toTop, ↑(discreteIntTopModule).toModuleCat) from
      (topologicalFreeEvalCondensed S (g.comap f.hom.hom)).hom.app U h)
  ext u
  change (topologicalFreeEval T g).hom
      ((topologicalFreeMap f).hom
        ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)) =
    (topologicalFreeEval S (g.comap f.hom.hom)).hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u)
  have hn := congrArg (fun m : topologicalFree S ⟶ discreteIntTopModule => m.hom
      ((show C(↑U.unop.toTop, ↑(topologicalFree S).toModuleCat) from h) u))
    (topologicalFreeEval_naturality f g)
  simpa using hn

/-- `Z`-valued represented topological-free evaluation is natural in the light profinite source. -/
lemma topologicalFreeEvalDiscrete_naturality {S T : LightProfinite.{0}} (f : S ⟶ T)
    (g : LocallyConstant T ℤ) :
    topologicalFreeCondensedMap f ≫ topologicalFreeEvalDiscrete T g =
      topologicalFreeEvalDiscrete S (g.comap f.hom.hom) := by
  simpa [topologicalFreeEvalDiscrete, Category.assoc] using
    congrArg (fun m => m ≫ discreteIntTopModuleCondensedIso.hom)
      (topologicalFreeEvalCondensed_naturality f g)

/-- The represented evaluation induced by `f` sends the Dirac section to `f`. -/
lemma topologicalFreeEvalDiscrete_diracSection (f : LocallyConstant S ℤ) :
    ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      ((topologicalFreeEvalDiscrete S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))) = f := by
  rw [show topologicalFreeEvalDiscrete S f =
    topologicalFreeEvalCondensed S f ≫ discreteIntTopModuleCondensedIso.hom by rfl]
  change ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).inv.app (ModuleCat.of ℤ ℤ)).hom.app ⟨S⟩
      (discreteIntTopModuleCondensedIso.hom.hom.app ⟨S⟩
        ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
          ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  rw [discreteIntTopModuleCondensedIso_sections]
  change (show LocallyConstant S ℤ from discreteIntTopModuleSectionsEquiv S
      ((topologicalFreeEvalCondensed S f).hom.app ⟨S⟩
        ((coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)))) = f
  ext s
  dsimp [discreteIntTopModuleSectionsEquiv, discreteIntTopModulePresheafIso,
    topologicalFreeEvalCondensed]
  change (topologicalFreeEval S f).hom
      ((show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)) s) = f s
  rw [topologicalFreeDiracSection_yoneda_apply]
  exact topologicalFreeEval_single S f s

/-- The sheaf-level morphism induced by the presheaf comparison from formal free sections to
represented topological-free sections. -/
noncomputable def freePresheafComparisonSheafification :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S where
  hom := CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

@[reassoc (attr := simp)]
lemma toSheafify_freePresheafComparisonSheafification :
    CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom =
    freePresheafToTopologicalFreePresheaf S := by
  exact CategoryTheory.toSheafify_sheafifyLift (coherentTopology LightProfinite)
    (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property

/-- At the represented identity section, the free/sheaf adjunction unit is the sheafification of
the presheaf free generator. -/
lemma freeForgetAdjunction_unit_app_id :
    ((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S) =
      (CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S)) := by
  rw [LightCondensed.freeForgetAdjunction, CategoryTheory.Sheaf.adjunction_unit_app_hom]
  rfl

/-- The sheafified presheaf comparison sends the represented Dirac generator to the represented
topological Dirac section. -/
lemma freePresheafComparison_diracSection :
    (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S)).app ⟨S⟩
        (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S) := by
  have h := congrArg (fun η : freePresheaf S ⟶ topologicalFreePresheaf S =>
      η.app ⟨S⟩ (ModuleCat.freeMk (𝟙 S)))
    (toSheafify_freePresheafComparisonSheafification S)
  change ((CategoryTheory.toSheafify (coherentTopology LightProfinite) (freePresheaf S) ≫
      (freePresheafComparisonSheafification S).hom).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  exact h.trans (by
    change (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (freePresheafToTopologicalFreePresheaf S).app ⟨S⟩ (ModuleCat.freeMk (𝟙 S))) =
      (show C(↑S.toTop, ↑(topologicalFree S).toModuleCat) from
        (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S))
    rw [freePresheafToTopologicalFreePresheaf_app_freeMk]
    ext s
    rw [topologicalFreeDiracSection_yoneda_apply]
    rfl)

/-- Under the free/forget adjunction, the sheafified presheaf comparison is characterized by the
represented topological Dirac section. -/
lemma freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freePresheafComparisonSheafification S) = topologicalFreeDiracSection S := by
  apply (coherentTopology LightProfinite).yonedaEquiv.injective
  rw [GrothendieckTopology.yonedaEquiv_apply]
  rw [Adjunction.homEquiv_apply]
  change (freePresheafComparisonSheafification S).hom.app ⟨S⟩
      (((LightCondensed.freeForgetAdjunction ℤ).unit.app S.toCondensed).hom.app ⟨S⟩ (𝟙 S)) =
    (coherentTopology LightProfinite).yonedaEquiv (topologicalFreeDiracSection S)
  rw [freeForgetAdjunction_unit_app_id]
  exact freePresheafComparison_diracSection S

/-- The canonical comparison from the free light condensed abelian group to the light condensed
abelian group represented by the free topological abelian group. -/
noncomputable def freeToTopologicalFree :
    (free ℤ).obj S.toCondensed ⟶ topologicalFreeCondensed S :=
  ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)).symm
    (topologicalFreeDiracSection S)

@[simp]
lemma freeForgetAdjunction_homEquiv_freeToTopologicalFree :
    (LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed (topologicalFreeCondensed S)
      (freeToTopologicalFree S) = topologicalFreeDiracSection S := by
  simp [freeToTopologicalFree]

/-- The existing `freeToTopologicalFree` morphism is the sheaf-level morphism induced by the
presheaf comparison. -/
lemma freeToTopologicalFree_eq_sheafified_presheaf_comparison :
    freeToTopologicalFree S = freePresheafComparisonSheafification S := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed S)).injective
  rw [freeForgetAdjunction_homEquiv_freeToTopologicalFree,
    freeForgetAdjunction_homEquiv_freePresheafComparisonSheafification]

/-- The comparison from the free light condensed abelian group to the represented topological free
abelian group is natural in the light profinite source. -/
lemma freeToTopologicalFree_naturality {S T : LightProfinite.{0}} (f : S ⟶ T) :
    ((free ℤ).map (lightProfiniteToLightCondSet.map f)) ≫ freeToTopologicalFree T =
      freeToTopologicalFree S ≫ topologicalFreeCondensedMap f := by
  apply ((LightCondensed.freeForgetAdjunction ℤ).homEquiv S.toCondensed
    (topologicalFreeCondensed T)).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeToTopologicalFree]
  simp
  exact topologicalFreeDiracSection_naturality f

/-- The represented topological-free sheaf is isomorphic to its sheafification. -/
private noncomputable def topologicalFreeCondensedSheafifyIso (S : LightProfinite.{0}) :
    topologicalFreeCondensed S ≅
      (CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).obj
        (topologicalFreePresheaf S) where
  hom := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).hom)
  inv := CategoryTheory.ObjectProperty.homMk ((CategoryTheory.isoSheafify
    (coherentTopology LightProfinite) (topologicalFreeCondensed S).property).inv)
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (CategoryTheory.isoSheafify (coherentTopology LightProfinite)
      (topologicalFreeCondensed S).property).inv_hom_id

/-- The sheafified presheaf comparison is the comparison followed by the inverse sheafification
identification of the represented target. -/
private lemma sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv
    (S : LightProfinite.{0}) :
    (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S)) ≫
        (topologicalFreeCondensedSheafifyIso S).inv) =
      freePresheafComparisonSheafification S := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [topologicalFreeCondensedSheafifyIso]
  rw [CategoryTheory.isoSheafify_inv]
  change CategoryTheory.sheafifyMap (coherentTopology LightProfinite)
      (freePresheafToTopologicalFreePresheaf S) ≫
        CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
          (𝟙 (topologicalFreePresheaf S)) (topologicalFreeCondensed S).property =
      CategoryTheory.sheafifyLift (coherentTopology LightProfinite)
        (freePresheafToTopologicalFreePresheaf S) (topologicalFreeCondensed S).property
  rw [CategoryTheory.sheafifyMap_sheafifyLift]
  simp

private instance instIsIso_sheafifiedPresheafComparison (S : LightProfinite.{0}) :
    IsIso (((CategoryTheory.presheafToSheaf (coherentTopology LightProfinite) (ModuleCat.{0} ℤ)).map
      (freePresheafToTopologicalFreePresheaf S))) := by
  rw [← CategoryTheory.GrothendieckTopology.W_iff]
  exact (coherentTopology LightProfinite).W_of_isLocallyBijective
    (freePresheafToTopologicalFreePresheaf S)

instance instIsIso_freeToTopologicalFree (S : LightProfinite.{0}) :
    IsIso (freeToTopologicalFree S) := by
  rw [freeToTopologicalFree_eq_sheafified_presheaf_comparison]
  rw [← sheafified_presheaf_comparison_comp_topologicalFreeCondensedSheafifyIso_inv]
  exact IsIso.comp_isIso' (instIsIso_sheafifiedPresheafComparison S) (Iso.isIso_inv _)

noncomputable def freeTopologicalFreeIso (S : LightProfinite.{0}) :
    (free ℤ).obj S.toCondensed ≅ topologicalFreeCondensed S :=
  asIso (freeToTopologicalFree S)

lemma freeTopologicalFreeIso_hom (S : LightProfinite.{0}) :
    (freeTopologicalFreeIso S).hom = freeToTopologicalFree S := by
  rfl

/-- Applying the comparison to a section transported back along `freeTopologicalFreeIso.symm`
recovers the original represented topological-free section. -/
@[simp]
lemma freeToTopologicalFree_app_section_of_iso_symm
    (T X : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩) :
    (freeToTopologicalFree T).hom.app ⟨X⟩
      ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s) = s := by
  change ((freeTopologicalFreeIso T).hom.hom.app ⟨X⟩)
      ((freeTopologicalFreeIso T).inv.hom.app ⟨X⟩ s) = s
  change ((freeTopologicalFreeIso T).inv ≫ (freeTopologicalFreeIso T).hom).hom.app ⟨X⟩ s = s
  simp

/-- Restrictions of a free section pulled back from the represented topological-free sheaf are
identified by applying the free/topological-free comparison. -/
@[simp]
lemma freeToTopologicalFree_app_map_section_of_iso_symm
    (T X Y : LightProfinite.{0}) (s : (topologicalFreeCondensed T).obj.obj ⟨X⟩)
    (f : Y ⟶ X) :
    (freeToTopologicalFree T).hom.app ⟨Y⟩
      (((free ℤ).obj T.toCondensed).obj.map f.op
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) =
      (topologicalFreeCondensed T).obj.map f.op s := by
  have hX := freeToTopologicalFree_app_section_of_iso_symm T X s
  have hn := ConcreteCategory.congr_hom ((freeToTopologicalFree T).hom.naturality f.op)
    ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)
  change (freeToTopologicalFree T).hom.app ⟨Y⟩
      (((free ℤ).obj T.toCondensed).obj.map f.op
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) =
    (topologicalFreeCondensed T).obj.map f.op
      ((freeToTopologicalFree T).hom.app ⟨X⟩
        ((freeTopologicalFreeIso T).symm.hom.hom.app ⟨X⟩ s)) at hn
  rw [hX] at hn
  exact hn

/-- The free/topological-free comparison is injective on sections over every light profinite. -/
lemma freeToTopologicalFree_app_injective
    (T X : LightProfinite.{0}) :
    Function.Injective ((freeToTopologicalFree T).hom.app ⟨X⟩) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

/-- A free section is determined by its image in the represented topological-free sheaf. -/
lemma freeSection_eq_of_freeToTopologicalFree_eq
    (T X : LightProfinite.{0})
    {u v : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩}
    (h : (freeToTopologicalFree T).hom.app ⟨X⟩ u =
      (freeToTopologicalFree T).hom.app ⟨X⟩ v) :
    u = v :=
  freeToTopologicalFree_app_injective T X h

/-- Convenience form for comparing free sections by comparing the resulting measures pointwise
after applying the free/topological-free comparison. -/
lemma freeSection_map_eq_of_pointwise_measure_eq
    (T X : LightProfinite.{0})
    {u v : ((free ℤ).obj T.toCondensed).obj.obj ⟨X⟩}
    (h : ∀ x : X,
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
        (freeToTopologicalFree T).hom.app ⟨X⟩ u) x =
      (show C(↑X.toTop, ↑(topologicalFree T).toModuleCat) from
        (freeToTopologicalFree T).hom.app ⟨X⟩ v) x) :
    u = v := by
  apply freeSection_eq_of_freeToTopologicalFree_eq T X
  apply ContinuousMap.ext
  intro x
  exact h x

abbrev freeLightProfiniteMap : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ⟶
    sequentialToLightCondSet.obj (lightCondSetToSequential.obj
      ((forget ℤ).obj ((free ℤ).obj S.toCondensed))) :=
  LightCondSet.sequentialAdjunction.unit.app <| (forget ℤ).obj <| (free ℤ).obj S.toCondensed

namespace FreeImage

open LightProfinite.FreeImage

def iso : (forget ℤ).obj ((free ℤ).obj S.toCondensed) ≅
    sequentialToLightCondSet.obj (sequential S) := sorry

end FreeImage

/-- The sequential finite-measure model for the free light condensed abelian group on `S`. -/
abbrev freeMeasureSequential : Sequential :=
  LightProfinite.FreeImage.sequential S

/-- The comparison isomorphism from the underlying light condensed set of `ℤ[S]` to the sequential
finite-measure model.  The proof is currently the main remaining comparison input in this file. -/
noncomputable def freeMeasureModelIso :
    (forget ℤ).obj ((free ℤ).obj S.toCondensed) ≅
      sequentialToLightCondSet.obj (freeMeasureSequential S) :=
  FreeImage.iso S

instance : IsIso (freeLightProfiniteMap S) := by
  erw [sequentialAdjunction.isIso_unit_app_iff_mem_essImage]
  exact ⟨_, ⟨(FreeImage.iso S).symm⟩⟩

end LightCondAb
