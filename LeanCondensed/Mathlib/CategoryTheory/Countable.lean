import Mathlib.CategoryTheory.Countable

universe u

noncomputable section

open CategoryTheory Quiver Countable

instance {J : Type u} [Countable J] [Category J] [Quiver.IsThin J] :
    CountableCategory J :=
  CountableCategory.mk inferInstance (fun _ _ ↦ ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩)

noncomputable instance {J : Type u} [Finite J] [Category J] [Quiver.IsThin J] : FinCategory J := by
  apply FinCategory.mk (Fintype.ofFinite J) (fun j j' ↦ Fintype.ofFinite (j ⟶ j'))
