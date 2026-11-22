import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceIndTopology
import Mathlib.Algebra.Field.TransferInstance

/-!
# The transported local field structure on the arithmetic unit perfection

`SourceUnitPerfection place` is the localization of the actual integral
unit group at the nonzero integers. Its actual logarithm is a `ℚ`-linear
equivalence to the actual algebraic closure `SourceAlgebraicClosure place`
(IUT III, Remark 3.1.1: `log(αF_v) ≅ k`).

This file transports the field structure of `SourceAlgebraicClosure place`
back along that equivalence. The resulting multiplication is the
logarithmic transport of the field multiplication, not the original
multiplication of units. The same underlying equivalence is then a ring
equivalence for the transported structure.

Scope: this is only the local carrier packaging `log(αF_v) ≅ k`. It does
not construct the tensor packet, integral structures, arithmetic tensor
carriers, or any poly-isomorphism, and it does not close N5/N7.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Transport the field structure of `SourceAlgebraicClosure place` to
`SourceUnitPerfection place` along the logarithmic `ℚ`-linear equivalence
`sourceUnitPerfectionEquiv place`. The transported multiplication is
`x * y = e.symm (e x * e y)`; it is not the original unit multiplication. -/
@[reducible]
noncomputable def sourceUnitPerfectionField (place : NumberField.FinitePlace K) :
    Field (SourceUnitPerfection place) :=
  (sourceUnitPerfectionEquiv place).toEquiv.field

/-- The logarithmic equivalence, regarded as a ring equivalence for the
transported field structure. -/
noncomputable def sourceUnitPerfectionRingEquiv (place : NumberField.FinitePlace K) :
    letI := (sourceUnitPerfectionEquiv place).toEquiv.add
    letI := (sourceUnitPerfectionEquiv place).toEquiv.mul
    SourceUnitPerfection place ≃+* SourceAlgebraicClosure place :=
  letI := (sourceUnitPerfectionEquiv place).toEquiv.add
  letI := (sourceUnitPerfectionEquiv place).toEquiv.mul
  Equiv.ringEquiv (sourceUnitPerfectionEquiv place).toEquiv
/-- The underlying function of the transported ring equivalence is exactly
`sourceUnitPerfectionEquiv place`. -/
theorem sourceUnitPerfectionRingEquiv_apply (place : NumberField.FinitePlace K)
    (x : SourceUnitPerfection place) :
    letI := (sourceUnitPerfectionEquiv place).toEquiv.add
    letI := (sourceUnitPerfectionEquiv place).toEquiv.mul
    sourceUnitPerfectionRingEquiv place x = sourceUnitPerfectionEquiv place x :=
  rfl

end

end LeanFormal.IUT.NumberFieldFinitePlace








