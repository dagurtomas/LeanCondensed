import Mathlib.Topology.LocallyConstant.Algebra

namespace LocallyConstant

variable {X Y Z : Type*} [TopologicalSpace X]

/-- `LocallyConstant.map` as a `MulHom`. -/
@[to_additive (attr := simps) "`LocallyConstant.map` as an `AddHom`."]
noncomputable
def mapMulHom [Mul Y] [Mul Z] (f : Y →ₙ* Z) :
    LocallyConstant X Y →ₙ* LocallyConstant X Z where
  toFun := map f
  map_mul' := by aesop

/-- `LocallyConstant.map` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`LocallyConstant.map` as an `AddMonoidHom`."]
noncomputable
def mapMonoidHom [MulOneClass Y] [MulOneClass Z] (f : Y →* Z) :
    LocallyConstant X Y →* LocallyConstant X Z where
  toFun := map f
  map_one' := by aesop
  map_mul' := by aesop

/-- `LocallyConstant.map` as a linear map. -/
@[simps!]
noncomputable
def mapₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (f : Y →ₗ[R] Z) :
    LocallyConstant X Y →ₗ[R] LocallyConstant X Z where
  toFun := map f
  map_add' := by aesop
  map_smul' := by aesop

/-- `LocallyConstant.map` as a `RingHom`. -/
@[simps!]
noncomputable
def mapRingHom [Semiring Y] [Semiring Z] (f : Y →+* Z) :
    LocallyConstant X Y →+* LocallyConstant X Z where
  toMonoidHom := mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

/-- `LocallyConstant.comap` as an `AlgHom` -/
@[simps!]
noncomputable
def mapₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (f : Y →ₐ[R] Z) : LocallyConstant X Y →ₐ[R] LocallyConstant X Z where
  toRingHom := mapRingHom f
  commutes' _ := by aesop
