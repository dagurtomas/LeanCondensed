module

public import LeanCondensed.Projects.SolidProjectiveGenerator.BoundedRetract
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The bounded-sequence shift-retract data of Lemma 3.3.3. -/
noncomputable def boundedShiftRetractData :
    CategoryTheory.ShiftRetractData solidification where
  xObj := P ℤ ⊗ boundedIntSequences
  aObj := P ℤ
  bObj := boundedIntSequences
  s := (oneMinusShift ℤ) ▷ boundedIntSequences
  toB := boundedTailMap
  toA := boundedDifferenceMap
  g := basisMap
  comm := boundedShiftRetract_comm
  sect := boundedTailSection
  sect_fac := boundedTailSection_fac
  inverted := solidification_map_oneMinusShift_tensor_isIso boundedIntSequences

/-- The split-epimorphism retract obtained from the bounded shift-retract diagram. -/
noncomputable def solidifiedBoundedRetractSolidP :
    Retract (solidification.obj boundedIntSequences) solidP :=
  boundedShiftRetractData.retract

/-- Fallback `SPG9-retract-only`: the bounded diagram makes
`solidification.map basisMap` a split epimorphism. -/
lemma SPG9_retract_only :
    solidifiedBoundedRetractSolidP.i ≫ solidification.map basisMap =
      𝟙 (solidification.obj boundedIntSequences) := by
  change (boundedShiftRetractData.retract).i ≫ solidification.map basisMap =
    𝟙 (solidification.obj boundedIntSequences)
  change (boundedShiftRetractData.retract).i ≫ (boundedShiftRetractData.retract).r =
    𝟙 (solidification.obj boundedIntSequences)
  exact boundedShiftRetractData.retract.retract

end ProjectiveGeneratorProof
end Solid
end LightCondensed
