/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.Category.LightProfinite.Sequence
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Spectral.Prespectral

open CategoryTheory Limits LightProfinite OnePoint

namespace LightCondensed

noncomputable section

variable (R : Type _) [CommRing R]

def ι : LightProfinite.of PUnit.{1} ⟶ ℕ∪{∞} :=
  (ConcreteCategory.ofHom ⟨fun _ ↦ ∞, continuous_const⟩)

def ι_split : SplitMono ι where
  retraction := (ConcreteCategory.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩)
  id := rfl

def P_map :
    (free R).obj (LightProfinite.of PUnit.{1}).toCondensed ⟶ (free R).obj (ℕ∪{∞}).toCondensed :=
  (lightProfiniteToLightCondSet ⋙ free R).map ι

def P : LightCondMod R := cokernel (P_map R)

def P_proj : (free R).obj (ℕ∪{∞}).toCondensed ⟶ P R := cokernel.π _

def PSequence : ShortComplex (LightCondMod R) :=
  ShortComplex.mk (P_map R) (P_proj R) (cokernel.condition _)

lemma PSequence_exact : (PSequence R).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (SplitMono.mono ((ι_split).map (lightProfiniteToLightCondSet ⋙ free R)))
    coequalizer.π_epi
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero,
    ←kernel.condition (P_proj R)]
  rfl

def PSequence_split : (PSequence R).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (PSequence_exact R).exact _
    ((ι_split).map (lightProfiniteToLightCondSet ⋙ free R)).id
    coequalizer.π_epi

def P_proj_split : SplitEpi (P_proj R) where
  section_ := (PSequence_split R).s
  id := (PSequence_split R).s_g

def P_retract : Retract (P R) ((free R).obj (ℕ∪{∞}).toCondensed) where
  i := _
  r := _
  retract := (PSequence_split R).s_g

def P_homMk (A : LightCondMod R) (f : (free R).obj (ℕ∪{∞}).toCondensed ⟶ A)
    (hf : P_map R ≫ f = 0) : P R ⟶ A := cokernel.desc _ f hf
