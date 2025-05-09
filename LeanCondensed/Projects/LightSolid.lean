/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Condensed.Discrete.Basic
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.Epi
import Mathlib.Topology.Category.LightProfinite.Sequence
import LeanCondensed.Mathlib.Condensed.Light.Limits
import LeanCondensed.Mathlib.Condensed.Light.Monoidal
import LeanCondensed.LightCondensed.Yoneda
import LeanCondensed.Projects.InternallyProjective
import LeanCondensed.Projects.LightProfiniteInjective
/-!

# Project: light solid abelian groups

-/
noncomputable section

universe u

open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed

attribute [local instance] Types.instConcreteCategory Types.instFunLike

section MonoidalClosed

variable (R : Type u) [CommRing R]

variable (A : LightCondMod R) (S : LightProfinite)

def ihom_points (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :=
  (LightCondensed.freeYoneda _ _ _).symm.trans ((ihom.adjunction A).homEquiv _ _).symm
-- We have an `R`-module structure on `M ⟶ N` for condensed `R`-modules `M`, `N`,
-- and this could be made an `≅`. But it's not needed in this proof.

lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B) :
    ∀ x, ConcreteCategory.hom (((ihom P).map e).val.app ⟨S⟩) x =
        (ihom_points R P B S).symm (ihom_points R P A S x ≫ e) := by
  intro x
  apply (ihom_points R P B S).injective
  simp only [ihom_points, freeYoneda, tensorLeft_obj, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply]
  erw [← Adjunction.homEquiv_naturality_right_symm]
  erw [← Adjunction.homEquiv_naturality_right_symm]
  simp [LightCondensed.yoneda]
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  erw [Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.homEquiv_symm_apply]
  ext
  simp [yonedaEquiv]
  rfl

lemma ihom_points_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : _ ⟶ _) :
    (ihom_points R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ConcreteCategory.hom (((ihom P).obj B).val.map π.op) ((ihom_points R P B S').symm f) := by
  simp [ihom_points]
  simp [freeYoneda, LightCondensed.yoneda]
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
    Adjunction.homEquiv_apply]
  simp only [Functor.comp_obj, tensorLeft_obj, ihom.ihom_adjunction_unit, Functor.map_comp]
  simp only [← Functor.map_comp]
  rw [(ihom P).map_comp, ← ihom.coev_naturality_assoc]
  simp only [tensorLeft_obj, Functor.map_comp]
  rw [Adjunction.unit_naturality_assoc]
  erw [Equiv.trans_apply, Equiv.trans_apply, yonedaEquiv_comp,
    Functor.FullyFaithful.homEquiv_apply, yonedaEquiv_comp]
  simp only [comp_val, yonedaEquiv, yoneda_obj_obj, Opposite.op_unop, Equiv.coe_fn_mk,
    FunctorToTypes.comp]
  erw [← (((LightCondensed.forget R).map ((ihom P).map f)).val.naturality_apply π.op)]
  simp only [ConcreteCategory.hom]
  apply congrArg
  simp only [← FunctorToTypes.comp]
  erw [← ((LightCondensed.forget R).map ((ihom.coev P).app ((free R).obj
    S'.toCondensed))).val.naturality_apply]
  simp only [ConcreteCategory.hom, FunctorToTypes.comp]
  apply congrArg
  have : (lightProfiniteToLightCondSet.map π).val.app (Opposite.op S) (𝟙 S) =
      S'.toCondensed.val.map π.op (𝟙 S') := rfl
  rw [this]
  simp
  rfl

def tensorFreeIso (X Y : LightCondSet.{u}) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⨯ Y) :=
  Functor.Monoidal.μIso (free R) X Y ≪≫ ((free R).mapIso
    ((ChosenFiniteProducts.product X Y).isLimit.conePointUniqueUpToIso (limit.isLimit (pair X Y))))

def tensorFreeIso' (S T : LightProfinite) :
    (free R).obj S.toCondensed ⊗ (free R).obj T.toCondensed ≅
      (free R).obj (S ⨯ T).toCondensed := tensorFreeIso R S.toCondensed T.toCondensed ≪≫
        (free R).mapIso (Limits.PreservesLimitPair.iso lightProfiniteToLightCondSet _ _).symm

instance (A : LightCondMod R) : PreservesColimits (tensorRight A) := by
  sorry

instance : Linear R (LightCondMod R) := inferInstanceAs (Linear R (Sheaf _ _))

instance : MonoidalLinear R (LightCondMod R) := by sorry

def tensorCokerIso {A B C : LightCondMod R} (f : A ⟶ B) : cokernel f ⊗ C ≅ cokernel (f ▷ C) :=
  preservesColimitIso (tensorRight C) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl (by simp))

end MonoidalClosed

namespace LightProfinite

def shift : ℕ∪{∞} ⟶ ℕ∪{∞} := TopCat.ofHom {
  toFun
    | ∞ => ∞
    | OnePoint.some n => (n + 1 : ℕ)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat, Filter.tendsto_add_atTop_iff_nat, tendsto_atTop_nhds]
    intro U h hU
    simp only [isOpen_iff_of_mem h, isClosed_discrete, isCompact_iff_finite, true_and] at hU
    refine ⟨sSup (Option.some ⁻¹' U)ᶜ + 1, fun n hn ↦ by
      simpa using not_mem_of_csSup_lt (Nat.succ_le_iff.mp hn) (Set.Finite.bddAbove hU)⟩ }

end LightProfinite

namespace LightCondensed

variable (R : Type _) [CommRing R]
-- might need some more assumptions eventually, finite type over `ℤ`?

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  constructor
  · intro ⟨h⟩ A B e he S g
    have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihom_points R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihom_points _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihom_points R P B S').symm.injective
    rw [hh]
    exact ihom_points_symm_comp R B P S' S π g
  · intro h
    constructor
    constructor
    intro A B e he
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihom_points _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihom_points _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihom_points_symm_comp R B P S' S π ((ihom_points R P B S) g)
    erw [hh] at this
    simp [this]
    rfl

def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map (TopCat.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

def P : LightCondMod R := cokernel (P_map R)

def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf

instance : InternallyProjective (P R) := by
  rw [internallyProjective_iff_tensor_condition]
  intro A B e he S g
  sorry

instance : InternallyProjective ((free R).obj (ℕ∪{∞}).toCondensed) := sorry

variable (R : Type) [CommRing R]

example : Abelian (LightCondMod R) := by infer_instance

example (A B : LightCondMod R) : AddCommGroup (A ⟶ B) := by infer_instance

def one_minus_shift' : (free R).obj (ℕ∪{∞}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _  - (lightProfiniteToLightCondSet ⋙ free R).map LightProfinite.shift

def one_minus_shift : P R ⟶ P R := by
  refine P_homMk R _ (one_minus_shift' R) ?_ ≫ P_proj R
  simp [one_minus_shift']
  sorry

abbrev induced_from_one_minus_shift (A : LightCondMod R) :
    ((ihom (P R)).obj A) ⟶ ((ihom (P R)).obj A) :=
  (pre (one_minus_shift R)).app A

variable {R : Type} [CommRing R]

/-- A light condensed `R`-module `A` is *solid* if the shift map `ℕ∪∞ → ℕ∪∞` induces an isomorphism
on internal homs into `A` -/
class IsSolid (A : LightCondMod R) : Prop where
  one_minus_shift_induces_iso : IsIso ((pre (one_minus_shift R)).app A)

structure Solid (R : Type) [CommRing R] where
  toLightCondMod : LightCondMod R
  [isSolid : IsSolid toLightCondMod]

namespace Solid

def of (A : LightCondMod R) [IsSolid A] : Solid R := ⟨A⟩

instance category : Category (Solid R) :=
  InducedCategory.category toLightCondMod

instance : IsSolid ((discrete (ModuleCat R)).obj (ModuleCat.of R R)) := sorry

instance : Inhabited (Solid R) := ⟨Solid.of ((discrete (ModuleCat R)).obj (ModuleCat.of R R))⟩

@[simps!]
def solidToCondensed (R : Type) [CommRing R] : Solid R ⥤ LightCondMod R :=
  inducedFunctor _

def solidification  (R : Type) [CommRing R] : LightCondMod R ⥤ Solid R := sorry

def _root_.LightCondMod.solidify (A : LightCondMod R) : Solid R := (solidification R).obj A

def val (A : Solid R) : LightCondMod R := A.toLightCondMod -- maybe unnecessary, `A.1` is fine.

def solidificationAdjunction (R : Type) [CommRing R] : solidification R ⊣ solidToCondensed R :=
  sorry

instance : (solidification R).IsLeftAdjoint := (solidificationAdjunction R).isLeftAdjoint

instance : (solidToCondensed R).IsRightAdjoint := (solidificationAdjunction R).isRightAdjoint

open MonoidalCategory

/- This is the monoidal structure on localized categories -/
instance : MonoidalCategory (Solid R) := sorry

instance : HasLimitsOfSize.{u, 0} Type := inferInstance

instance : Category.{0, 1} (ModuleCat R) := inferInstance

instance : SmallCategory.{1} (LightCondMod R) := inferInstance

variable (A : LightCondMod R)

instance : HasLimitsOfSize.{0, 0} (ModuleCat R) := inferInstance

instance : HasLimitsOfSize.{0, 0} (LightCondMod R) :=
  show (HasLimitsOfSize (Sheaf _ _)) from inferInstance

instance : HasLimitsOfSize.{0, 0} (Solid R) := sorry

instance : HasColimits (Solid R) := sorry

example : PreservesLimits (solidToCondensed R) := inferInstance

instance : PreservesColimits (solidToCondensed R) := sorry

-- TODO: define this property:
-- instance : PreservesExtensions (solidToCondensed R) := sorry

end Solid

end LightCondensed
