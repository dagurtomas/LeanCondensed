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

/-- Formal SPG9 reduction: once `solidification.map basisMap` is known to be mono, the split-epi
retract from the bounded shift diagram is automatically the two-sided inverse. -/
lemma boundedShiftRetract_idempotent_eq_identity_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    solidification.map basisMap ≫ (boundedShiftRetractData.retract).i =
      𝟙 (solidification.obj (P ℤ)) := by
  apply (cancel_mono (solidification.map basisMap)).1
  calc
    (solidification.map basisMap ≫ (boundedShiftRetractData.retract).i) ≫
        solidification.map basisMap
        = solidification.map basisMap ≫
            ((boundedShiftRetractData.retract).i ≫ solidification.map basisMap) := by
          rw [Category.assoc]
    _ = solidification.map basisMap ≫ 𝟙 (solidification.obj boundedIntSequences) := by
          change solidification.map basisMap ≫
            ((boundedShiftRetractData.retract).i ≫ (boundedShiftRetractData.retract).r) =
              solidification.map basisMap ≫ 𝟙 (solidification.obj boundedIntSequences)
          exact congrArg (fun q => solidification.map basisMap ≫ q)
            boundedShiftRetractData.retract.retract
    _ = 𝟙 (solidification.obj (P ℤ)) ≫ solidification.map basisMap := by
          simp

/-- Conditional isomorphism statement for SPG9.  The remaining mathematical input is the mono
property of `solidification.map basisMap`. -/
lemma isIso_solidification_map_basisMap_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    IsIso (solidification.map basisMap) :=
  boundedShiftRetractData.isIso_map_g
    boundedShiftRetract_idempotent_eq_identity_of_solidified_basisMap_mono

/-- Conditional bounded-sequence identification; this becomes the SPG9 isomorphism once the mono
property of `solidification.map basisMap` is supplied. -/
noncomputable def solidPIsoBounded_of_solidified_basisMap_mono
    [Mono (solidification.map basisMap)] :
    solidP ≅ solidification.obj boundedIntSequences := by
  letI := isIso_solidification_map_basisMap_of_solidified_basisMap_mono
  exact asIso (solidification.map basisMap)

end ProjectiveGeneratorProof
end Solid
end LightCondensed
