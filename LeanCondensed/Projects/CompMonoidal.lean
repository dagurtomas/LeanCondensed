import Mathlib

open CategoryTheory MonoidalCategory Functor Category Functor.Monoidal
  Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Functor.Monoidal

variable {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (L : C ⥤ D) [L.Monoidal] [L.EssSurj] (F : D ⥤ E) [(L ⋙ F).Monoidal]

def coreMonoidalOfComp : F.CoreMonoidal where
  εIso := εIso (L ⋙ F) ≪≫ F.mapIso (εIso L).symm
  μIso X Y := sorry
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

def monoidalOfComp : F.Monoidal := sorry

end CategoryTheory.Functor.Monoidal
