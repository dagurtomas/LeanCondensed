import Mathlib.CategoryTheory.Countable

universe u

noncomputable section

open CategoryTheory Quiver Countable

instance {J : Type u} [ctble : Countable J] [Category J] [thin : Quiver.IsThin J]: CountableCategory J :=
  CountableCategory.mk ctble (fun _ _ ↦ ⟨fun _ ↦ 0, fun _ _ _ ↦ (thin _ _).elim _ _⟩)

noncomputable instance {J : Type u} [fin : Finite J] [Category J] [thin : Quiver.IsThin J] : FinCategory J := by
  apply FinCategory.mk (Fintype.ofFinite J) (fun j j' ↦ Fintype.ofFinite (j ⟶ j'))
