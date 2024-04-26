import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T)
variable (D : Type*) [Category D]
variable [HasWeakSheafify J D]

instance : IsIso (constantPresheafAdj D hT).unit := by
  simp only [constantPresheafAdj, Functor.comp_obj, evaluation_obj_obj, Functor.id_obj,
    Adjunction.mkOfUnitCounit_unit]
  infer_instance

-- How generally does this hold?
instance : IsIso (constantSheafAdj J D hT).unit := by
  simp only [constantSheafAdj, Adjunction.comp, Functor.comp_obj, sheafToPresheaf_obj,
    evaluation_obj_obj]
  refine @IsIso.comp_isIso _ _ _ _ _ (constantPresheafAdj D hT).unit _ inferInstance ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ inferInstance
  -- intro X
  -- simp only [Functor.comp_obj, evaluation_obj_obj, Functor.const_obj_obj, sheafToPresheaf_obj,
  --   whiskerLeft_app, whiskerRight_app, Functor.id_obj, sheafificationAdjunction_unit_app,
  --   evaluation_obj_map]
  -- simp only [toSheafify]
  apply (config := { allowSynthFailures := true }) isIso_whiskerLeft
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro F
  simp only [Functor.comp_obj, Functor.id_obj, evaluation_obj_obj, sheafToPresheaf_obj,
    whiskerRight_app, sheafificationAdjunction_unit_app, evaluation_obj_map]
  simp only [toSheafify]

  -- apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso
  -- apply (config := { allowSynthFailures := true }) NatIso.isIso_app_of_isIso

  -- apply (config := { allowSynthFailures := true }) isIso_whiskerRight
  --apply (sheafificationAdjunction J D).isIso_unit_of_iso
  sorry
