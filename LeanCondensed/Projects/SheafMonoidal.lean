import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Sites.ChosenFiniteProducts
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import LeanCondensed.Projects.LocalizedMonoidal


universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor.Monoidal

-- variable {C : Type*} [Category C] (m₁ m₂ : MonoidalCategory)


end CategoryTheory.Functor.Monoidal

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

attribute [local instance] Types.instConcreteCategory

section

variable {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) [J.PreservesSheafification F] [HasWeakSheafify J A] [HasWeakSheafify J B]
    [MonoidalCategory A] [MonoidalCategory B] [F.Monoidal]
    [(J.W (A := A)).IsMonoidal] [(J.W (A := B)).IsMonoidal]

attribute [local instance] monoidalCategory

-- noncomputable instance : (presheafToSheaf _ _ ⋙ composeAndSheafify J F).Monoidal :=
--   monoidalTransport (presheafToSheafCompComposeAndSheafifyIso J F).symm

-- noncomputable instance : (composeAndSheafify J F).Monoidal :=
--   Localization.Monoidal.functorMonoidalOfComp (presheafToSheaf _ _) J.W (Iso.refl _) _

end

section

variable {A : Type*} [Category A]
    (F : Type (max u v) ⥤ A) [J.PreservesSheafification F] [HasWeakSheafify J A]
    [MonoidalCategory A] [F.Monoidal]
    [(J.W (A := A)).IsMonoidal]

noncomputable instance :
    letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
    (presheafToSheaf _ _ ⋙ composeAndSheafify J F).Monoidal :=
  letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
  monoidalTransport (presheafToSheafCompComposeAndSheafifyIso J F).symm

noncomputable instance foo :
    letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
    (composeAndSheafify J F).Monoidal := by
  letI : MonoidalCategory (Sheaf J A) := monoidalCategory J A
  letI : (presheafToSheaf J (Type (max u v))).Monoidal := sorry
  exact
    Functor.Monoidal.instComp (sheafToPresheaf J (Type (max u v)))
      ((whiskeringRight Cᵒᵖ (Type (max u v)) A).obj F ⋙ presheafToSheaf J A)


end

end CategoryTheory.Sheaf
