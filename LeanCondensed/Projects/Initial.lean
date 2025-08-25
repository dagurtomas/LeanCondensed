/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Category.LightProfinite.Basic

open CategoryTheory

universe u

def empty_elim {p : Sort u} {X : LightProfinite} (hX : ¬ Nonempty X) (x : X) : p := (hX ⟨x⟩).elim

def empty_subset {X : LightProfinite} (hX : ¬ Nonempty X) (s : Set X) : s = ⊤ := by
  ext x
  exact empty_elim hX x

def empty_map {X Y : LightProfinite} (hY : ¬ Nonempty Y) (f : X ⟶ Y) : ¬ Nonempty X :=
  fun h ↦ h.elim (fun x ↦ hY ⟨f x⟩)

def empty_iso {X Y : LightProfinite} (hY : ¬ Nonempty Y) (f : X ⟶ Y) : IsIso f := by
  let finv : Y ⟶ X := CompHausLike.ofHom _ {
    toFun y := empty_elim hY y
    continuous_toFun := by
      apply Continuous.mk
      intro s empty_elim
      rw [empty_subset hY ((fun y ↦ _root_.empty_elim hY y) ⁻¹' s)]
      exact TopologicalSpace.isOpen_univ }
  refine IsIso.mk ⟨finv, ?_⟩
  constructor <;> ext x
  exact empty_elim hY (f x)
  exact empty_elim hY x
