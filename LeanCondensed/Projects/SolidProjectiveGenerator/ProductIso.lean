module

public import LeanCondensed.Projects.SolidProjectiveGenerator.BoundedIso
public import LeanCondensed.Projects.SolidProjectiveGenerator.RealVanishing
@[expose] public section

noncomputable section

open CategoryTheory Limits LightCondensed LightProfinite MonoidalCategory MonoidalClosed OnePoint
open scoped BigOperators

namespace LightCondensed
namespace Solid
namespace ProjectiveGeneratorProof

/-- The solidification of `P ℤ` is the countable product of copies of `ℤ`, obtained by composing
its identification with bounded integer sequences and the real-vanishing product comparison. -/
noncomputable def solidPIsoProduct : solidP ≅ productInt :=
  solidPIsoBounded ≪≫ solidBoundedIsoProduct

lemma solidPIsoProduct_hom_eq :
    solidPIsoProduct.hom =
      (solidPIsoBounded ≪≫ solidBoundedIsoProduct).hom :=
  rfl

end ProjectiveGeneratorProof
end Solid
end LightCondensed
