import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

instance : R.IsLeftKanExtension adj.unit where
  nonempty_isUniversal := sorry

instance : L.IsRightKanExtension adj.counit := sorry
