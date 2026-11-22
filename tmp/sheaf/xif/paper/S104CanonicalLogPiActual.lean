import tmp.sheaf.xif.paper.S101UniformizerChangeActual
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-! # S104: canonical logPi and the exact dependence of boundaryLogWithFor

boundaryLogWithFor pi hpi logPi x depends on the chosen scalar logPi only
linearly: for fixed pi/hpi/x,

  boundaryLogWithFor ... logPi x - boundaryLogWithFor ... logPi' x
    = n • (logPi - logPi').

The p-adic log series of the source is defined near 1; on a uniformizer pi it
would require a logarithm of pi itself, which is not supplied by the p-adic
unit logarithm API.  This file records the exact missing canonical logPi and
does not fabricate one.

No fake canonical log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S104CanonicalLogPiActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
variable (pi : Integers (CommonPrimeCompletion place))
variable (hpi : Irreducible pi)

/-- boundaryLogWithFor depends on logPi only by the scalar n • logPi. -/
theorem boundaryLogWithFor_logPi_difference
    (logPi logPi' : CommonPrimeCompletion place)
    (x : sourceOBoundaryMonoid place) :
    boundaryLogWithFor place pi hpi logPi x -
      boundaryLogWithFor place pi hpi logPi' x =
      ((boundaryUnitDecompositionFor place pi hpi x).n : ℤ) •
        (logPi - logPi') := by
  unfold boundaryLogWithFor
  module

/-- Candidate from the p-adic log1p series: log1p(pi) = log(1 + pi), NOT the
p-adic logarithm of pi.  It is recorded only to show that log1p does not give
the uniformizer logarithm. -/
def candidateLog1pPi : CommonPrimeCompletion place :=
  log1p (pi : CommonPrimeCompletion place)

/-- Exact missing canonical logPi: a logarithm of the chosen uniformizer
compatible with the p-adic/local-field logarithm, not the log1p(pi) candidate. -/
structure CanonicalLogPiData where
  uniformizer : Integers (CommonPrimeCompletion place)
  uniformizer_eq : uniformizer = pi
  logPi : CommonPrimeCompletion place
  logPi_eq_log_pi : Prop
  compatible_with_unitLog : Prop

/-- Exact missing canonical logPi; no inhabitant asserted. -/
def CanonicalLogPiRequired : Prop :=
  Nonempty (CanonicalLogPiData (K := K) (p := p) place pi)

end LeanFormal.IUT.XiFPaper.S104CanonicalLogPiActual

end
