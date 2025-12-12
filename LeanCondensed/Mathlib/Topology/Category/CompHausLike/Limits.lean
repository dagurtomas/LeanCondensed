import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Topology.Category.LightProfinite.Limits

open CategoryTheory Topology

namespace CompHausLike

universe u

section BinaryCoproducts

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike P)

/--
A typeclass describing the property that forming the disjoint union is stable under the
property `P`.
-/
abbrev HasExplicitBinaryCoproduct := HasProp P (X ⊕ Y)

variable [HasExplicitBinaryCoproduct X Y]

/--
The coproduct of two objects in `CompHausLike`, constructed as the disjoint
union with its usual topology.
-/
def coprod : CompHausLike P := CompHausLike.of P (X ⊕ Y)

/--
The inclusion of the left factor into the explicit binary coproduct.
-/
def coprod.inl : X ⟶ coprod X Y := ofHom _ { toFun := fun x ↦ Sum.inl x }

/--
The inclusion of the right factor into the explicit binary coproduct.
-/
def coprod.inr : Y ⟶ coprod X Y := ofHom _ { toFun := fun x ↦ Sum.inr x }

variable {X Y}

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def coprod.desc {B : CompHausLike P} (l : X ⟶ B) (r : Y ⟶ B) : coprod X Y ⟶ B :=
  ofHom _ { toFun := Sum.elim l r }

@[reassoc (attr := simp)]
lemma coprod.inl_desc {B : CompHausLike P} (l : X ⟶ B) (r : Y ⟶ B) :
    coprod.inl X Y ≫ coprod.desc l r = l := rfl

@[reassoc (attr := simp)]
lemma coprod.inr_desc {B : CompHausLike P} (l : X ⟶ B) (r : Y ⟶ B) :
    coprod.inr X Y ≫ coprod.desc l r = r := rfl

@[ext]
lemma coprod.hom_ext {B : CompHausLike P} (f g : coprod X Y ⟶ B)
    (hl : coprod.inl X Y ≫ f = coprod.inl X Y ≫ g) (hr : coprod.inr X Y ≫ f = coprod.inr X Y ≫ g) :
    f = g := by
  ext ⟨⟩
  exacts [ConcreteCategory.congr_hom hl _, ConcreteCategory.congr_hom hr _]

variable (X Y)

/-- The coproduct cocone associated to the explicit finite coproduct. -/
abbrev coprod.binaryCofan : Limits.BinaryCofan X Y :=
  Limits.BinaryCofan.mk (coprod.inl X Y) (coprod.inr X Y)

/-- The explicit finite coproduct cocone is a colimit cocone. -/
def coprod.isColimit : Limits.IsColimit (coprod.binaryCofan X Y) := by
  refine Limits.BinaryCofan.isColimitMk (fun s ↦ ofHom _ { toFun := Sum.elim s.inl s.inr }) ?_ ?_ ?_
  all_goals cat_disch

lemma coprod.inl_injective : Function.Injective (coprod.inl X Y) :=
  Sum.inl_injective

lemma coprod.inr_injective : Function.Injective (coprod.inr X Y) :=
  Sum.inr_injective

lemma coprod.inl_inr_jointly_surjective (r : coprod X Y) :
    (∃ x : X, r = coprod.inl _ _ x) ∨ (∃ y : Y, r = coprod.inr _ _ y) := by
  obtain (r | r) := r
  exacts [Or.inl ⟨r, rfl⟩, Or.inr ⟨r, rfl⟩]

-- lemma finiteCoproduct.ι_desc_apply {B : CompHausLike P} {π : (a : α) → X a ⟶ B} (a : α) :
--     ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
--   tauto

instance : Limits.HasBinaryCoproduct X Y where
  exists_colimit := ⟨coprod.binaryCofan X Y, coprod.isColimit X Y⟩

variable (P) in
/--
A typeclass describing the property that forming all finite disjoint unions is stable under the
property `P`.
-/
class HasExplicitBinaryCoproducts : Prop where
  hasProp (X Y : CompHausLike.{u} P) : HasExplicitBinaryCoproduct X Y

attribute [instance] HasExplicitBinaryCoproducts.hasProp

instance [HasExplicitBinaryCoproducts P] : Limits.HasBinaryCoproducts (CompHausLike P) :=
  Limits.hasBinaryCoproducts_of_hasColimit_pair _

/-- The inclusion maps into the explicit finite coproduct are open embeddings. -/
lemma coprod.isOpenEmbedding_inl : IsOpenEmbedding (coprod.inl X Y) :=
  IsOpenEmbedding.inl

/-- The inclusion maps into the explicit finite coproduct are open embeddings. -/
lemma coprod.isOpenEmbedding_inr : IsOpenEmbedding (coprod.inr X Y) :=
  IsOpenEmbedding.inr

instance : HasExplicitBinaryCoproducts
    (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X) where
  hasProp _ _ := { hasProp := ⟨inferInstance, inferInstance⟩ }

end BinaryCoproducts
