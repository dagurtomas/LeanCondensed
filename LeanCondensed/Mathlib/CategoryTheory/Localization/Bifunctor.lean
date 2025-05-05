import Mathlib.CategoryTheory.Localization.Bifunctor

namespace CategoryTheory

open Category

variable {C₁ C₂ D₁ D₂ E E' : Type*} [Category C₁] [Category C₂]
  [Category D₁] [Category D₂] [Category E] [Category E']

namespace Localization

section

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']

noncomputable instance Lifting₂.compRight {E' : Type*} [Category E'] [Lifting₂ L₁ L₂ W₁ W₂ F F']
    (G : E ⥤ E') :
    Lifting₂ L₁ L₂ W₁ W₂
      (F ⋙ (whiskeringRight _ _ _).obj G)
      (F' ⋙ (whiskeringRight _ _ _).obj G) := ⟨isoWhiskerRight (iso L₁ L₂ W₁ W₂ F F')
        ((whiskeringRight _ _ _).obj G)⟩

end

end Localization

end CategoryTheory
