import tmp.sheaf.xif.paper.S132FormalLogVolumeActual
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum

/-! # S142: normalized O-boundary log-volume from the formal boundary log

Using the formal boundary log (S111/S126), define the normalized K-valued
log-volume coordinate

  boundaryLogVolumeNormalized x
    = (logShellScale p)^{-1} * boundaryLogNormalized x.

On O-times this is exactly the scaled source integral-unit log used by the
actual source log-shell datum.  The integer formal-logPi coordinate is the
separate DVR exponent.

Uniformizer change: the integer coordinate changes by n - n'; the normalized
K-valued coordinate changes by the actual scaled unit-log difference.  It is not
declared invariant unless the unit-log difference is quotiented; the exact
correction is recorded.

No fake field log/real log-volume/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S142NormalizedBoundaryLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual
open LeanFormal.IUT.XiFPaper.S87OBoundaryDecompositionActual
open LeanFormal.IUT.XiFPaper.S101UniformizerChangeActual
open LeanFormal.IUT.XiFPaper.S111FormalBoundaryLogActual
open LeanFormal.IUT.XiFPaper.S126FormalBoundaryLogUseActual
open LeanFormal.IUT.XiFPaper.S132FormalLogVolumeActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Normalized K-valued log-volume coordinate from the formal boundary log. -/
noncomputable def boundaryLogVolumeNormalized
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    CommonPrimeCompletion place :=
  (logShellScale p : CommonPrimeCompletion place)⁻¹ *
    boundaryLogNormalized (K := K) (p := p) place x

/-- The source log-shell log coordinate, typed in the common completion. -/
noncomputable def sourceLogShellLog
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    CommonPrimeCompletion place := by
  exact Multiplicative.toAdd ((sourceLocalLogShellDatum (p := p) place).logMap u)

/-- On O-times the normalized boundary log-volume is exactly the scaled source
log-shell log coordinate. -/
theorem boundaryLogVolumeNormalized_eq_sourceLogMap
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    boundaryLogVolumeNormalized (K := K) (p := p) place
        (sourceOTimesToBoundary (K := K) (p := p) place u) =
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        sourceLogShellLog (K := K) (p := p) place u := by
  unfold sourceLogShellLog
  unfold boundaryLogVolumeNormalized
  rw [boundaryLogNormalized_eq_sourceLogMap]
  rfl

/-- Normalized K-valued log-volume in terms of the DVR unit and exponent. -/
theorem boundaryLogVolumeNormalized_eq_scale_mul_unitLog
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    boundaryLogVolumeNormalized (K := K) (p := p) place x =
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        unitLog (K := CommonPrimeCompletion place)
          (boundaryUnitDecomposition (K := K) (p := p) place x).u := by
  unfold boundaryLogVolumeNormalized boundaryLogNormalized boundaryLogFormal
  dsimp only

/-- Uniformizer change of the normalized K-valued log-volume: the exact scaled
unit-log correction. -/
theorem boundaryLogVolumeNormalized_change
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        (boundaryLogFormalFor place pi hpi x).1 -
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        (boundaryLogFormalFor place pi' hpi' x).1 =
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        (unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor place pi hpi x).u -
          unitLog (K := CommonPrimeCompletion place)
            (boundaryUnitDecompositionFor place pi' hpi' x).u) := by
  rw [← mul_sub, boundaryLogFormalFor_change_normalized]

/-- The integer formal-logPi coordinate changes by n - n'. -/
theorem boundaryLogVolumeInteger_change
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) :
    (boundaryLogFormalFor place pi hpi x).2 -
        (boundaryLogFormalFor place pi' hpi' x).2 =
      ((boundaryUnitDecompositionFor place pi hpi x).n : ℤ) -
        ((boundaryUnitDecompositionFor place pi' hpi' x).n : ℤ) :=
  boundaryLogFormalFor_change_integer (K := K) (p := p) place pi pi' hpi hpi' x

/-- The normalized coordinate is invariant only after quotienting the actual
unit-log correction.  This Prop records the exact condition. -/
def NormalizedInvariantCondition
    (pi pi' : Integers (CommonPrimeCompletion place))
    (hpi : Irreducible pi) (hpi' : Irreducible pi')
    (x : sourceOBoundaryMonoid (K := K) (p := p) place) : Prop :=
  unitLog (K := CommonPrimeCompletion place)
      (boundaryUnitDecompositionFor place pi hpi x).u =
    unitLog (K := CommonPrimeCompletion place)
      (boundaryUnitDecompositionFor place pi' hpi' x).u

end LeanFormal.IUT.XiFPaper.S142NormalizedBoundaryLogVolumeActual

end
