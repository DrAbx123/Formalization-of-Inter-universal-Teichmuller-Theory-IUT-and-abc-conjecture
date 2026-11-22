import tmp.sheaf.xif.paper.S21cActualQUnitBridgeActual
import tmp.sheaf.xif.paper.PaperSourceThetaConsistencyActual

/-! # S21d: actual correction factor for the source theater vs qVFamily q

The source theater packet q and the qVFamily q norm are not identified in the
source.  This file constructs the actual real correction factor

  sourceTheaterQCorrectionFactor
    = sourceThetaQ T b / theaterPacket.q

and proves the corrected log equality

  log ||sourceQVFamilyUnit||
    = log (thetaValueAt oneLabel) + log correctionFactor.

Thus the mismatch is handled by an actual factor, not hidden.  The field/place
comparison between T.arithmetic.F and I.initial.arithmetic.Fmod is a separate
actual map requirement; its exact structure is recorded, not faked.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21dSourceTheaterCorrectionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S21cActualQUnitBridgeActual
open LeanFormal.IUT.XiFPaper.S21bCompletionThetaNormBridgeActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (n : ThetaPilotCarrier l)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}

/-- The actual real correction factor between the qVFamily norm and the source
theater packet q. -/
noncomputable def sourceTheaterQCorrectionFactor : Real :=
  sourceThetaQ T b / (I.theaterAt (n.val : Int) 0).thetaPacket.q

theorem sourceTheaterQCorrectionFactor_pos :
    0 < sourceTheaterQCorrectionFactor (l := l) T b n (I := I) := by
  unfold sourceTheaterQCorrectionFactor
  exact div_pos (sourceThetaQ_pos (l := l) T b)
    (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos

/-- Actual constructed packet q is the source q norm. -/
theorem actualS21ThetaPacket_q :
    (actualS21ThetaPacket (l := l) T b).q = sourceThetaQ T b := rfl

/-- Actual corrected log equality: the qVFamily unit log equals the source
theta log plus the correction-factor log. -/
theorem sourceThetaLog_eq_thetaLog_add_correction :
    Real.log ‖(actualS21QUnit (l := l) T b :
        CommonPrimeCompletion (sourceThetaPlace T b))‖ =
      Real.log (I.thetaValueAt (n.val : Int) 0 (oneLabel l)) +
        Real.log (sourceTheaterQCorrectionFactor (l := l) T b n (I := I)) := by
  rw [actualS21QUnit_norm, actualS21ThetaPacket_q,
    thetaValueAt_one_eq_q (l := l) I n]
  unfold sourceTheaterQCorrectionFactor
  rw [Real.log_div (sourceThetaQ_pos (l := l) T b).ne'
    (I.theaterAt (n.val : Int) 0).thetaPacket.q_pos.ne']
  ring

/-- The actual correction factor is the exact norm ratio. -/
theorem correctionFactor_eq_norm_ratio :
    sourceTheaterQCorrectionFactor (l := l) T b n (I := I) =
      ‖(actualS21QUnit (l := l) T b :
        CommonPrimeCompletion (sourceThetaPlace T b))‖ /
        (I.theaterAt (n.val : Int) 0).thetaPacket.q := by
  unfold sourceTheaterQCorrectionFactor
  rw [actualS21QUnit_norm, actualS21ThetaPacket_q]

/-- Exact actual field/place comparison requirement between the qVFamily
F-place and the source theater Fmod place. -/
structure SourceTheaterFieldComparison where
  fieldMap : I.initial.arithmetic.Fmod →+* T.arithmetic.F
  placeMap : FinitePlaceAtPrime I.initial.arithmetic.Fmod (qVFamTensorP T b) →
    FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b)
  placeCompatible : Prop
  qUnitTransport : Prop

/-- The exact field/place comparison requirement; no inhabitant asserted. -/
def SourceTheaterFieldComparisonRequired : Prop :=
  Nonempty (SourceTheaterFieldComparison (T := T) (b := b) (I := I))

/-- Exact obstruction to using the hardcoded source theater q correction as an
equality: the field/place comparison is required. -/
def SourceTheaterQCorrectionActualGap : Prop :=
  SourceTheaterQCorrectionRequired (l := l) T b n (I := I) ∧
    SourceTheaterFieldComparisonRequired (T := T) (b := b) (I := I)

end LeanFormal.IUT.XiFPaper.S21dSourceTheaterCorrectionActual

end
