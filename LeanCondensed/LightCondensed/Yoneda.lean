import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module

universe u

noncomputable section

open CategoryTheory

namespace LightCondensed

variable (R : Type _) [Ring R] -- might need some more assumptions

@[simps! apply]
def yoneda (S : LightProfinite.{u}) (A : LightCondSet) :
    (S.toCondensed ⟶ A) ≃ A.val.obj ⟨S⟩ :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans yonedaEquiv

@[simp]
lemma yoneda_symm_apply_val_app (S : LightProfinite) (A : LightCondSet)
    (a : A.val.obj ⟨S⟩) (Y : LightProfiniteᵒᵖ) (f : Y.unop ⟶ S) :
      ((yoneda S A).symm a).val.app Y f = A.val.map f.op a := rfl

abbrev forgetYoneda (S : LightProfinite) (A : LightCondMod R) :
    (S.toCondensed ⟶ (forget R).obj A) ≃ A.val.obj ⟨S⟩ := yoneda _ _

abbrev freeYoneda (S : LightProfinite) (A : LightCondMod R) :
    ((free R).obj S.toCondensed ⟶ A) ≃ A.val.obj ⟨S⟩ :=
  ((freeForgetAdjunction R).homEquiv _ _).trans (yoneda _ _)

-- lemma freeYoneda_symm_naturality (S T : LightProfinite) (A : LightCondMod R) (x : A.val.obj ⟨S⟩) :
--     False := by
--   have := ((freeYoneda R S A).symm x).val.naturality
  -- ((freeYoneda R S A).symm x).val.app ⟨T⟩ ≫ _ = _ ≫ _

-- TODO: add some naturality lemmas?

end LightCondensed
