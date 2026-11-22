import tmp.sheaf.xif.paper.S21fSourceTheaterFieldComparisonActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import tmp.sheaf.xif.paper.S21bCompletionThetaNormBridgeActual

/-! # S40: direct Fmod -> F RingHom/place map for fieldI

The donor-built source contract fieldI has V = NativePlaces X.S.  This file
works directly on fieldI's own arithmetic fields, with no transport to
FinitePrimePlace 2 7 and no dependent elimination of the donor equality.

Actual objects:

* fieldMap : fieldI.Fmod ->+* fieldI.F, the algebraMap of fieldI's arithmetic;
* placeMap : fieldI.Fmod-place -> fieldI.F-place, selectedCommonPrimePlace;
* placeMap compatibility with the base contraction;
* q correction factor and corrected q/theta transport using the actual qVFamily
  unit and its norm.

No reverse F -> Fmod map.

No fake dependent transport/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S40SourceTheaterFieldMapDirectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S21bCompletionThetaNormBridgeActual
open LeanFormal.IUT.XiFPaper.S21cActualQUnitBridgeActual
open LeanFormal.IUT.XiFPaper.S21dSourceTheaterCorrectionActual
open LeanFormal.IUT.XiFPaper.S21eSourceTheaterFieldComparisonActual
open LeanFormal.IUT.XiFPaper.S21fSourceTheaterFieldComparisonActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (D : NativeOriginalInputDonors (X := X))
variable (n : ThetaPilotCarrier l)
variable (p : Nat) [Fact p.Prime]

/-- Actual field map on fieldI itself: Fmod -> F. -/
noncomputable def sourceFieldMap :
    (fieldI (X := X) D).initial.arithmetic.Fmod →+*
      (fieldI (X := X) D).initial.arithmetic.F :=
  algebraMap (fieldI (X := X) D).initial.arithmetic.Fmod
    (fieldI (X := X) D).initial.arithmetic.F

/-- Actual place map on fieldI itself: Fmod-place -> F-place. -/
noncomputable def sourcePlaceMap
    (lower : FinitePlaceAtPrime
      (fieldI (X := X) D).initial.arithmetic.Fmod p) :
    FinitePlaceAtPrime (fieldI (X := X) D).initial.arithmetic.F p :=
  selectedCommonPrimePlace
    (k := (fieldI (X := X) D).initial.arithmetic.Fmod)
    (K := (fieldI (X := X) D).initial.arithmetic.F) (p := p) lower

/-- Actual compatibility of sourcePlaceMap with the base contraction. -/
theorem sourcePlaceMap_compatible
    (lower : FinitePlaceAtPrime
      (fieldI (X := X) D).initial.arithmetic.Fmod p) :
    relativeCommonPrimePlace
        (k := (fieldI (X := X) D).initial.arithmetic.Fmod)
        (K := (fieldI (X := X) D).initial.arithmetic.F)
        (sourcePlaceMap (X := X) D p lower) = lower :=
  relativeCommonPrimePlace_selected
    (k := (fieldI (X := X) D).initial.arithmetic.Fmod)
    (K := (fieldI (X := X) D).initial.arithmetic.F) (p := p) lower

/-- Actual correction factor for fieldI's theater packet q. -/
noncomputable def sourceFieldQCorrectionFactor (b : Bad (nativePlaceSelection X.S)) : Real :=
  sourceThetaQ X.S b /
    ((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q

/-- Corrected q transport: packet q times factor is the qVFamily norm. -/
theorem sourceFieldQCorrectionFactor_mul_q
    (b : Bad (nativePlaceSelection X.S)) :
    ((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q *
        sourceFieldQCorrectionFactor (X := X) D n b =
      sourceThetaQ X.S b := by
  unfold sourceFieldQCorrectionFactor
  have hq : ((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q ≠ 0 :=
    ((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q_pos.ne'
  field_simp [hq]

/-- Corrected log q/theta transport for fieldI. -/
theorem sourceFieldQCorrectionFactor_log
    (b : Bad (nativePlaceSelection X.S)) :
    Real.log ‖(actualS21QUnit (l := l) X.S b :
        CommonPrimeCompletion (sourceThetaPlace X.S b))‖ =
      Real.log ((fieldI (X := X) D).thetaValueAt (n.val : Int) 0 (oneLabel l)) +
        Real.log (sourceFieldQCorrectionFactor (X := X) D n b) := by
  rw [actualS21QUnit_norm, actualS21ThetaPacket_q]
  rw [thetaValueAt_one_eq_q (l := l) (I := fieldI (X := X) D) n]
  unfold sourceFieldQCorrectionFactor
  rw [Real.log_div (sourceThetaQ_pos (l := l) X.S b).ne'
    (((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q_pos).ne']
  ring

end LeanFormal.IUT.XiFPaper.S40SourceTheaterFieldMapDirectActual

end
