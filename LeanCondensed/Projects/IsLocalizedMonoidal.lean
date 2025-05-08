import LeanCondensed.Projects.LocalizedMonoidal

open CategoryTheory Localization.Monoidal MonoidalCategory

noncomputable section

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

variable [W.IsMonoidal] [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

instance : (L').IsLocalization W := inferInstanceAs (L.IsLocalization W)

variable [MonoidalCategory D]

namespace MonoidalCategory

@[simps!]
def equivLocalizedMonoidal : D ≌ LocalizedMonoidal L W ε := CategoryTheory.Equivalence.refl

open Functor.Monoidal Functor.LaxMonoidal Functor.OplaxMonoidal

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).inverse.Monoidal :=
  letI : (L ⋙ (equivLocalizedMonoidal L W ε).inverse).Monoidal := inferInstanceAs L.Monoidal
  functorMonoidalOfComp L W ε _

instance [L.Monoidal] : (equivLocalizedMonoidal L W ε).functor.Monoidal :=
  (equivLocalizedMonoidal L W ε).symm.inverseMonoidal
