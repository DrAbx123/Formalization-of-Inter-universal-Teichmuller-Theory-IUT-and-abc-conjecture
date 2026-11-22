import tmp.sheaf.xif.paper.S747ZeroLabelHullAuditActual
import tmp.sheaf.xif.paper.S874GlobalInterfaceFillActual
import tmp.sheaf.xif.paper.S154PaperNormalizedQUnitActual

/-! # S882: per-b corrected 2l is actual because the zero-inclusive root
Theta hull is the canonical unit region O, so perBThetaHullLog = 0.

Thus perBQPilotLog ≤ 0 ≤ 2l * 0 = 2l * perBThetaHullLog, and the global
corrected target follows by the actual Vbad weighted sum.  The paper hull
formula data remains an exact field. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S882PerBCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S747ZeroLabelHullAuditActual
open LeanFormal.IUT.XiFPaper.S874GlobalInterfaceFillActual
open LeanFormal.IUT.XiFPaper.S868GlobalPaperTargetInterfaceActual
open LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The zero-inclusive root Theta hull is exactly the closed unit region O. -/
theorem rootThetaHull_eq_canonicalUnitReference :
    rootThetaHull (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (rootHalfCoefficient (l := l) T b) =
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  rw [rootThetaHull_eq_closure_holomorphic (l := l) T b]
  exact (isCompact_arithmeticTupleCanonicalRegions
    (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed.closure_eq

/-- The old zero-inclusive per-b Theta hull log vanishes. -/
theorem perBThetaHullLog_eq_zero :
    perBThetaHullLog (l := l) T b = 0 := by
  unfold perBThetaHullLog rootThetaHullLog
  rw [rootThetaHull_eq_canonicalUnitReference (l := l) T b]
  exact arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar

/-- The actual per-b qPilot log is nonpositive. -/
theorem perBQPilotLog_nonpos :
    perBQPilotLog (l := l) T b ≤ 0 := by
  have h := perBQPilotLog_le_perBThetaHullLog (l := l) T b
  rwa [perBThetaHullLog_eq_zero (l := l) T b] at h

/-- Actual per-b corrected 2l inequality. -/
theorem correctedTargetPerB_actual :
    correctedTargetPerB (l := l) T := by
  intro b
  rw [perBThetaHullLog_eq_zero (l := l) T b]
  simpa using perBQPilotLog_nonpos (l := l) T b

/-- Actual global corrected target by Vbad weighted summation. -/
theorem correctedTarget_actual :
    S860GlobalCor312AuditActual.weightedQPilot T ≤
      (2 * (l.value : Real)) *
        S860GlobalCor312AuditActual.thetaHullScalar T :=
  correctedTarget_of_perB (l := l) T
    (correctedTargetPerB_actual (l := l) T)

/-- Actual global interface: correctedTarget and least-hull fields are filled;
only the paper hull formula data is recorded as an exact Prop. -/
noncomputable def globalPaperTargetInterfaceActual :
    GlobalPaperTargetInterface T :=
  globalPaperTargetInterfaceFilled (l := l) T
    (correctedTarget_actual (l := l) T)

end LeanFormal.IUT.XiFPaper.S882PerBCorrectedActual
end
