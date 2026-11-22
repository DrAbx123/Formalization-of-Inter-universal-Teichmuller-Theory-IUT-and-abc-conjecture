/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_RegularDifferentials
import tmp.external.ported.flt_core.Definitions.Def_ModularCurve_CanonicalDivisor
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_SerrePairing

/-! # A511 glue: regular-differential objects from the ported curve calculus -/

noncomputable section

namespace LeanFormal.IUT.Objects.RegularDifferential

open AlgebraicCurve KaehlerDifferential

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A regular differential object: a Kähler differential lying in the actual regular
differential submodule of the ported curve calculus. -/
structure RegularDifferentialObject where
  /-- The underlying Kähler differential. -/
  omega : Ω[F⁄K]
  /-- It is regular at every place. -/
  mem : omega ∈ AlgebraicCurve.regularDifferentials K F

/-- Recover the local coefficient condition from the ported `mem_regularDifferentials_iff`. -/
theorem RegularDifferentialObject.coeff_witness (D : RegularDifferentialObject K F) :
    ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, D.omega = f • v.dCoord := 
  (AlgebraicCurve.mem_regularDifferentials_iff (K := K) (F := F)).mp D.mem

/-- A regular differential has nonnegative order at every place (the different exponent is
nonnegative on the regular submodule). -/
theorem RegularDifferentialObject.ord_nonneg (D : RegularDifferentialObject K F)
    (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    0 ≤ v.ord (v.differentialCoeff D.omega) :=
  v.ord_differentialCoeff_nonneg_of_mem_regularDifferentials D.mem

/-- The zero regular differential object. -/
def regularDifferentialZero : RegularDifferentialObject K F where
  omega := 0
  mem := (AlgebraicCurve.regularDifferentials K F).zero_mem

end LeanFormal.IUT.Objects.RegularDifferential
