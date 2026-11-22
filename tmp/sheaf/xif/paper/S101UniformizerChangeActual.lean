import tmp.sheaf.xif.paper.S93BoundaryLogCompatibilityActual

/-! # S101: uniformizer-change formula for boundaryLogWith

For two uniformizers pi, pi' of the DVR Integers K and x in O-boundary,

  x = u * pi^n = u' * pi'^n',

with the chosen decompositions.  Hence

  boundaryLogWith pi logPi x - boundaryLogWith pi' logPi' x
    = n • logPi - n' • logPi' + (unitLog u - unitLog u').

The extra unit-log term is actual; the difference is not asserted to be only an
integer multiple of logPi.

No fake formula/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S93BoundaryLogCompatibilityActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- DVR decomposition data for a specified uniformizer. -/
structure OBoundaryUnitDecompFor
    (pi : Integers (CommonPrimeCompletion place)) (hpi : Irreducible pi)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) where
  n : ℕ
  u : (Integers (CommonPrimeCompletion place))ˣ
  eq : (x : CommonPrimeCompletion place) =
    (u : CommonPrimeCompletion place) * (pi : CommonPrimeCompletion place) ^ n

/-- Actual decomposition for a specified uniformizer. -/
noncomputable def boundaryUnitDecompositionFor
    (pi : Integers (CommonPrimeCompletion place)) (hpi : Irreducible pi)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    OBoundaryUnitDecompFor (K := K) (p := p) place pi hpi x := by
  letI : IsDiscreteValuationRing (Integers (CommonPrimeCompletion place)) :=
    isDiscreteValuationRingIntegers (K := CommonPrimeCompletion place) (p := p)
  have hx := boundaryToIntegers_ne_zero (K := K) (p := p) place x
  let hh := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := boundaryToIntegers (K := K) (p := p) place x) hx hpi
  let n := Classical.choose hh
  let u := Classical.choose (Classical.choose_spec hh)
  refine ⟨n, u, ?_⟩
  exact congrArg (fun z : Integers (CommonPrimeCompletion place) =>
    (z : CommonPrimeCompletion place))
    (Classical.choose_spec (Classical.choose_spec hh))

/-- Choice-dependent boundary log for a specified uniformizer. -/
noncomputable def boundaryLogWithFor
    (pi : Integers (CommonPrimeCompletion place)) (hpi : Irreducible pi)
    (logPi : CommonPrimeCompletion place)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place :=
  let d := boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x
  (d.n : ℤ) • logPi + unitLog (K := CommonPrimeCompletion place) d.u

/-- Actual change data for two uniformizers and the same O-boundary element. -/
noncomputable def uniformizerChangeData
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    OBoundaryUnitDecompFor (K := K) (p := p) place pi hpi x ×
      OBoundaryUnitDecompFor (K := K) (p := p) place pi' hpi' x :=
  (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x,
    boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x)

/-- Actual uniformizer-change formula, with the unit-log correction. -/
theorem boundaryLogWithFor_change
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (logPi logPi' : CommonPrimeCompletion place)
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryLogWithFor (K := K) (p := p) place pi hpi logPi x -
      boundaryLogWithFor (K := K) (p := p) place pi' hpi' logPi' x =
      ((boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).n : ℤ) •
          logPi -
        ((boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).n : ℤ) •
          logPi' +
        (unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).u -
          unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).u) := by
  unfold boundaryLogWithFor
  module

/-- The correction term is the actual unit-log difference; it is present in the
formula and is not simplified to an integer multiple of logPi. -/
noncomputable def unitLogCorrection
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place :=
  unitLog (K := CommonPrimeCompletion place)
      (boundaryUnitDecompositionFor (K := K) (p := p) place pi hpi x).u -
    unitLog (K := CommonPrimeCompletion place)
      (boundaryUnitDecompositionFor (K := K) (p := p) place pi' hpi' x).u

end LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual

end
