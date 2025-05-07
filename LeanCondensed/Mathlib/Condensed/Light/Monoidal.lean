import Mathlib
import LeanCondensed.Mathlib.CategoryTheory.Sites.Monoidal
import LeanCondensed.Mathlib.Condensed.Light.Small
import LeanCondensed.Mathlib.CategoryTheory.Monoidal.Braided.Transport
import LeanCondensed.Projects.SheafMonoidal

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

section

namespace CategoryTheory.MonoidalClosed -- TODO: move

instance {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Transported e) :=
  MonoidalClosed.ofEquiv _ (equivalenceTransported e).symm.toAdjunction

end CategoryTheory.MonoidalClosed

variable {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalCategory E] (F : Transported e ⥤ E)
    (G : E ⥤ Transported e)

def CategoryTheory.Equivalence.monoidalOfComp [(e.functor ⋙ F).Monoidal] : F.Monoidal :=
  monoidalTransport (e.invFunIdAssoc F)

def CategoryTheory.Equivalence.monoidalOfComp' [(G ⋙ e.inverse).Monoidal] : G.Monoidal :=
  letI : (G ⋙ (equivalenceTransported e).inverse ⋙ (equivalenceTransported e).functor).Monoidal :=
    inferInstanceAs
      ((G ⋙ (equivalenceTransported e).inverse) ⋙ (equivalenceTransported e).functor).Monoidal
  monoidalTransport (isoWhiskerLeft G e.counitIso ≪≫ G.rightUnitor)

end

namespace LightCondensed

attribute [local instance] monoidalCategory symmetricCategory

variable (R : Type u) [CommRing R]

instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : MonoidalCategory (Sheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)) :=
  inferInstanceAs (MonoidalCategory (LightCondMod.{u} R))

instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

local instance : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

-- Required to get sheafification.
-- TODO: add a global instance for sheafification of type-valued sheaves
attribute [local instance] Types.instConcreteCategory

instance : (presheafToSheaf _ _ ⋙ free R).Monoidal := sorry

def monoidalOfPostcomp {E : Type*} [Category E] [MonoidalCategory E] (F : E ⥤ LightCondMod.{u} R)
    [(F ⋙ (equivSmall _).functor).Monoidal] : F.Monoidal :=
  letI : (F ⋙ (equivSmall _).symm.inverse).Monoidal :=
    inferInstanceAs (F ⋙ (equivSmall _).functor).Monoidal
  (equivSmall (ModuleCat R)).symm.monoidalOfComp' F


def monoidalOfPrecomp {E : Type*} [Category E] [MonoidalCategory E] (F : LightCondSet.{u} ⥤ E)
    [((equivSmall _).inverse ⋙ F).Monoidal] : F.Monoidal :=
  letI : ((equivSmall _).symm.functor ⋙ F).Monoidal :=
    inferInstanceAs ((equivSmall _).inverse ⋙ F).Monoidal
  letI : (equivSmall (Type u)).symm.inverse.Monoidal := sorry
    -- ((Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts
    --   (equivSmall (Type u)).symm.inverse).mpr inferInstance).some
    -- The above is from a more recent mathlib
  monoidalTransport ((equivSmall _).symm.invFunIdAssoc F)

instance : (free R).Monoidal := by
  apply (config := {allowSynthFailures := true}) monoidalOfPostcomp
  apply (config := {allowSynthFailures := true}) monoidalOfPrecomp
  sorry
  -- Localization.Monoidal.functorMonoidalOfComp
  --   (presheafToSheaf _ _)
  --   ((coherentTopology LightProfinite.{u}).W (A := ModuleCat.{u} R))
  --   (Iso.refl _) _

end LightCondensed
