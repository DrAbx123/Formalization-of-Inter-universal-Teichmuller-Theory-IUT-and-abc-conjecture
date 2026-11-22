import tmp.sheaf.xif.paper.S1043CorrectedBridgeExactActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-! # S1050: perBQPilotLog coefficient audit

perBQPilotLog T b is qPilotClassicalLog with rootNormCoefficient (the classical
c_norm coefficient) and rootNormScalingData.  s994VR uses the finite-carrier
image of qPilotPaperRegion (paper cRoot region) under the actual S994
linearization, with the finite Haar measure.  These are different objects, not
definitionally equal.

Therefore globalQPilotLog (built from perBQPilotLog) is the CLASSICAL qPilot
object.  The paper global qPilot should be the weighted sum of the paper
per-b s994VR.  The exact identification is recorded as
S1050PerBQPaperExact / S1050PaperGlobalExact; no fake equality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- perBQPilotLog uses the classical rootNormCoefficient c_norm. -/
theorem s1050PerBQPilotLog_unfold
    (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog (l := l) T b =
      qPilotClassicalLog
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (Measure.addHaar)
        (rootNormCoefficient T b)
        (rootNormScalingData T b) := rfl

/-- globalQPilotLog is the classical perBQPilotLog weighted sum. -/
theorem s1050GlobalQPilotLog_unfold :
    globalQPilotLog (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * perBQPilotLog (l := l) T b := rfl

/-- s994VR is the finite-carrier image log of qPilotPaperRegion. -/
theorem s1050S994VR_unfold
    (In : S994FiniteInput T) (b : Bad (nativePlaceSelection T)) :
    s994VR (l := l) T In b =
      Real.log
        ((s994H (l := l) T b (In.L b)).measure
          (s994QPilotImage (l := l) T b (In.L b))).toReal := rfl

/-- The finite carrier image is the image of the paper qPilot region. -/
theorem s1050S994QPilotImage_unfold
    (In : S994FiniteInput T) (b : Bad (nativePlaceSelection T)) :
    s994QPilotImage (l := l) T b (In.L b) =
      (In.L b).e '' qPilotPaperRegion T b := rfl

/-- The paper global qPilot object: weighted sum of the paper per-b s994VR. -/
noncomputable def s1050PaperGlobalQPilotLog (In : S994FiniteInput T) : Real :=
  weightedPaperV (l := l) T (s994VR (l := l) T In)

/-- Definitional shape of the paper global qPilot. -/
theorem s1050PaperGlobalQPilotLog_unfold
    (In : S994FiniteInput T) :
    s1050PaperGlobalQPilotLog (l := l) T In =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * s994VR (l := l) T In b := rfl

/-- Exact per-b identification: classical perBQPilotLog equals paper s994VR. -/
def S1050PerBQPaperExact (In : S994FiniteInput T) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b = s994VR (l := l) T In b

/-- Exact global identification: classical globalQPilotLog equals paper global. -/
def S1050PaperGlobalExact (In : S994FiniteInput T) : Prop :=
  globalQPilotLog (l := l) T = s1050PaperGlobalQPilotLog (l := l) T In

/-- The exact per-b identification implies the exact global identification. -/
theorem s1050PaperGlobalExact_of_perB
    (In : S994FiniteInput T)
    (h : S1050PerBQPaperExact (l := l) T In) :
    S1050PaperGlobalExact (l := l) T In := by
  unfold S1050PaperGlobalExact s1050PaperGlobalQPilotLog
  unfold globalQPilotLog weightedPaperV
  apply Finset.sum_congr rfl
  intro b _
  rw [h b]

end LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual

end
