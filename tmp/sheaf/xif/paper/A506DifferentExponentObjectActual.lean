/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_RegularDifferentials
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_SerrePairing
import tmp.external.ported.flt_core.Definitions.Def_ModularCurve_CanonicalDivisor
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_SerrePairing

/-! # A506 object: different exponent object from the ported curve/different calculus -/

noncomputable section

namespace LeanFormal.IUT.Objects.Different

open AlgebraicCurve
open KaehlerDifferential

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable [Nontrivial Ω[F⁄K]]
variable [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]

/-- The different exponent object at a place: a nonzero Kähler differential together with
its explicit order at the place (the local different exponent).  Built from the ported
fermat/TauCeti curve calculus, not from an interface field. -/
structure DifferentExponentObject (v : AlgebraicCurve.Place K F) where
  /-- The chosen nonzero Kähler differential. -/
  omega : Ω[F⁄K]
  omega_ne_zero : omega ≠ 0
  /-- The local order of the differential at the place (different exponent). -/
  exponent : ℤ
  exponent_eq : exponent = v.ord (v.differentialCoeff omega)

/-- The different exponent object attached to an explicitly nonzero differential. -/
def differentExponentOf (v : AlgebraicCurve.Place K F) (omega : Ω[F⁄K])
    (h : omega ≠ 0) : DifferentExponentObject K F v where
  omega := omega
  omega_ne_zero := h
  exponent := v.ord (v.differentialCoeff omega)
  exponent_eq := rfl

/-- The stored exponent is exactly the local order of the differential coefficient. -/
theorem differentExponent_eq_ord (v : AlgebraicCurve.Place K F)
    (D : DifferentExponentObject K F v) :
    D.exponent = v.ord (v.differentialCoeff D.omega) := D.exponent_eq

/-- A regular differential has nonnegative local order: the different exponent is ≥ 0 on
regular differentials (Gap 1's positivity side). -/
theorem differentExponent_nonneg_of_mem_regularDifferentials
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (omega : Ω[F⁄K])
    (hω : omega ∈ AlgebraicCurve.regularDifferentials K F) :
    0 ≤ v.ord (v.differentialCoeff omega) :=
  AlgebraicCurve.Place.ord_differentialCoeff_nonneg_of_mem_regularDifferentials v hω

end LeanFormal.IUT.Objects.Different

