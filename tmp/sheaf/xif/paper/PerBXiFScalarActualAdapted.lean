import tmp.sheaf.xif.paper.QVFamRootCoefficientActual
import tmp.sheaf.xif.paper.QVPilotLatticeCoefficientPositiveActual
import tmp.sheaf.xif.paper.PaperXiFSpec
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# Per-b xi-f scalar from the 2l-th-root coefficient

Local root scalar: localQVRootLog b = -(c_root(b) log p_b), and
2l * localQVRootLog b = localQPilotLog b = -nativeQVPilotLocalMagnitude b.

The canonical procession is constant on this local scalar, so its average is
the local scalar.  Weighted summation gives

  globalRootLog = (1/(2l)) * nativeQVPilotNormalizedSignedLogVolume,

the root-normalized q-v scalar, not the old order scalar.  With
q = exp(globalRootLog), theta = globalRootLog, paperXiF follows from
-|log q| <= log q.

No fake inequality.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.PerBXiFScalarActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamRootCoefficientActual
open LeanFormal.IUT.XiFPaper.QVPilotLatticeCoefficientPositiveActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaperThetaHull

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Root local log is the full local q-pilot log divided by 2l. -/
theorem localQVRootLog_eq_localQPilotLog_div
    (b : Bad (nativePlaceSelection T)) :
    localQVRootLog T b = localQPilotLog T b / qVFamRootDenominator (l := l) := by
  rw [eq_div_iff (qVFamRootDenominator_ne_zero (l := l)), mul_comm]
  exact localQVRootLog_eq_half_localQPilotLog T b

/-- Root local log is the negative native local magnitude divided by 2l. -/
theorem localQVRootLog_eq_neg_magnitude_div
    (b : Bad (nativePlaceSelection T)) :
    localQVRootLog T b =
      - nativeQVPilotLocalMagnitude T b / qVFamRootDenominator (l := l) := by
  rw [localQVRootLog_eq_localQPilotLog_div, QVPilotLatticeCoefficientPositiveActual.localQPilotLog_eq_neg_nativeMagnitude]

/-- Canonical-procession average of the constant root local scalar. -/
noncomputable def perBRootProcessionAverage
    (b : Bad (nativePlaceSelection T)) : Real :=
  (canonicalProcession (l := l)).average
    (fun _ : SignedLabel l.value => localQVRootLog T b)

/-- The procession average is the local root scalar. -/
theorem perBRootProcessionAverage_eq
    (b : Bad (nativePlaceSelection T)) :
    perBRootProcessionAverage T b = localQVRootLog T b :=
  (canonicalProcession (l := l)).average_const (localQVRootLog T b)

/-- Global root q-pilot/theta-hull scalar: weighted sum of root local logs. -/
noncomputable def globalRootLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * localQVRootLog T b

/-- The global root scalar is (1/(2l)) times the native qVFamily signed scalar. -/
theorem globalRootLog_eq_rootNormalized :
    globalRootLog T =
      (qVFamRootDenominator (l := l))⁻¹ *
        nativeQVPilotNormalizedSignedLogVolume T := by
  unfold globalRootLog nativeQVPilotNormalizedSignedLogVolume
    nativeQVPilotNormalizedLogMagnitude
  calc
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * localQVRootLog T b)
        = ∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b *
              (localQPilotLog T b / qVFamRootDenominator (l := l)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [localQVRootLog_eq_localQPilotLog_div]
    _ = (∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b * localQPilotLog T b) /
          qVFamRootDenominator (l := l) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = (-∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b) /
          qVFamRootDenominator (l := l) := by
          congr 1
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro b _
          rw [QVPilotLatticeCoefficientPositiveActual.localQPilotLog_eq_neg_nativeMagnitude]
          ring
    _ = (qVFamRootDenominator (l := l))⁻¹ *
          (-∑ b : Bad (nativePlaceSelection T),
            nativeBadLocalWeight T b * nativeQVPilotLocalMagnitude T b) := by
          rw [div_eq_inv_mul]

/-- Paper q parameter from the root scalar. -/
noncomputable def paperRootQ : Real :=
  Real.exp (globalRootLog T)

/-- Its logarithm is the root scalar. -/
theorem log_paperRootQ :
    Real.log (paperRootQ T) = globalRootLog T := by
  unfold paperRootQ
  exact Real.log_exp _

/-- Paper-level paperXiF from the actual root scalar. -/
theorem paperXiF_root :
    paperXiF (paperRootQ T) (globalRootLog T) := by
  rw [paperXiF_iff, paperSignedLog_eq_neg_abs_log, log_paperRootQ]
  exact neg_abs_le (globalRootLog T)

/-- Actual per-b/global root data. -/
structure PerBRootXiFScalarData where
  rootCoefficient : Bad (nativePlaceSelection T) → Real
  rootCoefficient_eq : rootCoefficient = qVFamRootCoefficient T
  localRootLog : Bad (nativePlaceSelection T) → Real
  localRootLog_eq : localRootLog = localQVRootLog T
  processionAverage : Bad (nativePlaceSelection T) → Real
  processionAverage_eq : processionAverage = perBRootProcessionAverage T
  processionAverage_value : ∀ b, processionAverage b = localRootLog b
  globalRootLog : Real
  globalRootLog_eq : globalRootLog = PerBXiFScalarActualAdapted.globalRootLog T
  globalRootLog_eq_rootNormalized : globalRootLog =
    (qVFamRootDenominator (l := l))⁻¹ *
      nativeQVPilotNormalizedSignedLogVolume T

/-- Actual root scalar data. -/
noncomputable def perBRootXiFScalarData :
    PerBRootXiFScalarData T where
  rootCoefficient := qVFamRootCoefficient T
  rootCoefficient_eq := rfl
  localRootLog := localQVRootLog T
  localRootLog_eq := rfl
  processionAverage := perBRootProcessionAverage T
  processionAverage_eq := rfl
  processionAverage_value := perBRootProcessionAverage_eq T
  globalRootLog := globalRootLog T
  globalRootLog_eq := rfl
  globalRootLog_eq_rootNormalized := globalRootLog_eq_rootNormalized T

end LeanFormal.IUT.XiFPaper.PerBXiFScalarActualAdapted

end