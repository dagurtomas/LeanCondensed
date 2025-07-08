import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

-- This should be done for all concrete categories with a left adjoint to types.
variable (R : Type _) [Ring R]

@[simps! apply]
def yoneda (S : LightProfinite.{u}) (A : LightCondSet) :
    (S.toCondensed ⟶ A) ≃ A.val.obj ⟨S⟩ :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans yonedaEquiv

@[simp]
lemma yoneda_symm_apply_val_app (S : LightProfinite) (A : LightCondSet)
    (a : A.val.obj ⟨S⟩) (Y : LightProfiniteᵒᵖ) (f : Y.unop ⟶ S) :
      ((yoneda S A).symm a).val.app Y f = A.val.map f.op a := rfl

lemma yoneda_symm_naturality {S S' : LightProfinite} (f : S' ⟶ S) (A : LightCondSet)
    (x : A.val.obj ⟨S⟩) : lightProfiniteToLightCondSet.map f ≫ (yoneda S A).symm x =
      (yoneda S' A).symm ((A.val.map f.op) x) := by
  apply Sheaf.hom_ext
  rw [Sheaf.comp_val]
  ext T y
  simp only [FunctorToTypes.comp, yoneda_symm_apply_val_app, Opposite.op_unop]
  rw [← FunctorToTypes.map_comp_apply (F := A.val)]
  rfl

attribute [local instance] Types.instConcreteCategory Types.instFunLike
lemma yoneda_symm_conaturality (S : LightProfinite) {A A' : LightCondSet} (f : A ⟶ A')
    (x : A.val.obj ⟨S⟩) : (yoneda S A).symm x ≫ f = (yoneda S A').symm (f.val.app ⟨S⟩ x) := by
  apply Sheaf.hom_ext
  rw [Sheaf.comp_val]
  ext T y
  exact NatTrans.naturality_apply (φ := f.val) (Y := T) _ _

lemma yoneda_conaturality (S : LightProfinite) {A A' : LightCondSet} (f : A ⟶ A')
    (g : S.toCondensed ⟶ A) : f.val.app ⟨S⟩ (yoneda S A g) = yoneda S A' (g ≫ f) := rfl

abbrev forgetYoneda (S : LightProfinite) (A : LightCondMod R) :
    (S.toCondensed ⟶ (forget R).obj A) ≃ A.val.obj ⟨S⟩ := yoneda _ _

def freeYoneda (S : LightProfinite) (A : LightCondMod R) :
    ((free R).obj S.toCondensed ⟶ A) ≃ A.val.obj ⟨S⟩ :=
  ((freeForgetAdjunction R).homEquiv _ _).trans (yoneda _ _)

lemma freeYoneda_symm_naturality {S S' : LightProfinite} (f : S' ⟶ S) (A : LightCondMod R)
    (x : A.val.obj ⟨S⟩) : (lightProfiniteToLightCondSet ⋙ free R).map f ≫
      (freeYoneda R S A).symm x = (freeYoneda R S' A).symm ((A.val.map f.op) x) := by
  simp only [Functor.comp_obj, Functor.comp_map, freeYoneda, Equiv.symm_trans_apply,
    Adjunction.homEquiv_counit]
  simp only [← Category.assoc, ← Functor.map_comp]
  erw [yoneda_symm_naturality]
  rfl

lemma freeYoneda_symm_conaturality (S : LightProfinite) {A A' : LightCondMod R} (f : A ⟶ A')
    (x : A.val.obj ⟨S⟩) :
    (freeYoneda R S A).symm x ≫ f = (freeYoneda R S A').symm (f.val.app ⟨S⟩ x) := by
  simp only [freeYoneda, Equiv.symm_trans_apply]
  erw [← yoneda_symm_conaturality (S := S) (A' := (forget R).obj A') (f := (forget R).map f)]
  simp only [Adjunction.homEquiv_counit, Functor.id_obj, Category.assoc, Functor.map_comp,
    Adjunction.counit_naturality, Functor.comp_obj]
  rfl

end LightCondensed
