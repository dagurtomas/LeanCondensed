import Mathlib

example {J : Type*} {A : Type*} [DecidableEq J] {types : J → Type*}
    (nonempty : ∀j, Nonempty (types j)) (f : (j : J) → types j → A)
    (i : J) (t : types i) : ∃ (p : (Π(j : J), types j)), ∀ j, i = j → f j (p j) = f i t :=
  ⟨
    fun j ↦  (
      if hij : i = j then
        hij ▸ t
      else
        Classical.choice (nonempty j)
    ),
    by
      intro j h
      simp [dif_pos h]
      subst h
      rfl
  ⟩
