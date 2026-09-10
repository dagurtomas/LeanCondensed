import LeanCondensed.Projects.ClassicalSolidification

/- Run with `lake env lean Tests/SolidificationAxioms.lean` after `lake build LeanCondensed`. -/

/-- info: 'LightCondensed.Solid.solidification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LightCondensed.Solid.solidification

/-- info: 'LightCondensed.Solid.solidificationAdjunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LightCondensed.Solid.solidificationAdjunction

/-- info: 'LightCondAb.solidify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LightCondAb.solidify

/--
info: 'LightCondensed.Solid.Classical.solidificationFreeIsoDoubleDualFreeSolid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LightCondensed.Solid.Classical.solidificationFreeIsoDoubleDualFreeSolid

/--
info: 'LightCondensed.Solid.Classical.solidifiedFreeIsoClassicalCompletedFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LightCondensed.Solid.Classical.solidifiedFreeIsoClassicalCompletedFree

/--
info: 'LightCondensed.Solid.Classical.solidificationUnit_app_comp_solidifiedFreeIsoClassicalCompletedFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LightCondensed.Solid.Classical.solidificationUnit_app_comp_solidifiedFreeIsoClassicalCompletedFree
