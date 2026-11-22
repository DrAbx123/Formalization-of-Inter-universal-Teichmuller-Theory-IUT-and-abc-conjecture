import tmp.sheaf.xif.paper.S87OBoundaryDecompositionActual

/-! # S93: unit compatibility of the DVR boundary log

For a unit u embedded in O-boundary, the DVR decomposition has exponent n = 0
(valuation of a unit is zero), hence the boundary log is exactly unitLog u.
This proves the unit-log compatibility of boundaryLogWith.

Uniformizer change and a canonical logPi are recorded as explicit
choice/indeterminacy data; no fake independence is asserted.

No sorry, axiom, True, or PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S93BoundaryLogCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Unit compatibility: boundaryLogWith on the embedded unit u is unitLog u. -/
theorem boundaryLogWith_unit
    (logPi : CommonPrimeCompletion place)
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    boundaryLogWith (K := K) (p := p) place logPi
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      unitLog (K := CommonPrimeCompletion place) u := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  let x := sourceOTimesToBoundary (K := K) (p := p) place u
  let d := boundaryUnitDecomposition (K := K) (p := p) place x
  have hInt : boundaryToIntegers (K := K) (p := p) place x =
      d.u * (dvrUniformizer (K := K) (p := p) place) ^ d.n := by
    apply Subtype.ext
    exact d.eq
  have hx_int : boundaryToIntegers (K := K) (p := p) place x =
      (u : Integers (CommonPrimeCompletion place)) := by
    rfl
  have hval : d.n = 0 := by
    have hxunit : IsUnit (boundaryToIntegers (K := K) (p := p) place x) := by
      rw [hx_int]
      exact u.isUnit
    have hxzero : IsDiscreteValuationRing.addVal
        (Integers (CommonPrimeCompletion place))
        (boundaryToIntegers (K := K) (p := p) place x) = 0 :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hxunit
    have hpow : IsDiscreteValuationRing.addVal
        (Integers (CommonPrimeCompletion place))
        ((dvrUniformizer (K := K) (p := p) place) ^ d.n) = d.n := by
      simpa [nsmul_one] using
        (Irreducible.addVal_pow
          (dvrUniformizer_irreducible (K := K) (p := p) place) d.n)
    have hcongr := congrArg
      (IsDiscreteValuationRing.addVal (Integers (CommonPrimeCompletion place))) hInt
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit d.u,
      hpow, zero_add] at hcongr
    rw [hxzero] at hcongr
    exact_mod_cast hcongr.symm
  have hdu : d.u = u := by
    apply Units.ext
    have h := hInt
    rw [hval, pow_zero, mul_one] at h
    exact h.symm.trans hx_int
  have hd_eq : boundaryUnitDecomposition (K := K) (p := p) place x = d := rfl
  unfold boundaryLogWith
  dsimp only
  rw [hval, hdu]
  simp

/-- Exact uniformizer-change data: a second uniformizer and its chosen log,
with the actual decomposition exponent/unit of the same O-boundary element. -/
structure UniformizerChangeData
    (logPi logPi' : CommonPrimeCompletion place) where
  pi' : Integers (CommonPrimeCompletion place)
  pi'_irreducible : Irreducible pi'
  n : ℕ
  n' : ℕ
  u : (Integers (CommonPrimeCompletion place))ˣ
  u' : (Integers (CommonPrimeCompletion place))ˣ
  change_formula : Prop

/-- Exact missing canonical logPi: no canonical logarithm of the chosen
uniformizer is supplied by the source. -/
structure CanonicalLogPiRequired where
  logPi : CommonPrimeCompletion place
  canonical : Prop

end LeanFormal.IUT.XiFPaper.S93BoundaryLogCompatibilityActual

end
