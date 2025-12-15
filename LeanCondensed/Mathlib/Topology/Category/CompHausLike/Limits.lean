import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Topology.Category.LightProfinite.Limits

open CategoryTheory Topology Limits

namespace CompHausLike

universe u

section BinaryCoproducts

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike P)

section Coproduct

variable [HasProp P (X ⊕ Y)]

def coproductCocone : BinaryCofan X Y := BinaryCofan.mk (P := CompHausLike.of P (X ⊕ Y))
  (TopCat.ofHom { toFun := Sum.inl }) (TopCat.ofHom { toFun := Sum.inr })

def coproductIsColimit : IsColimit (coproductCocone X Y) := by
  refine BinaryCofan.isColimitMk (fun s ↦ ofHom _ { toFun := Sum.elim s.inl s.inr })
    (by cat_disch) (by cat_disch) fun _ _ h₁ h₂ ↦ ?_
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom h₁ _, ConcreteCategory.congr_hom h₂ _]

end Coproduct

end BinaryCoproducts
