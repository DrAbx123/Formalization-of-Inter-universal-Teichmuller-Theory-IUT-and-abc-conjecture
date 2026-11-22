import tmp.sheaf.xif.paper.S21eSourceTheaterFieldComparisonActual
import tmp.sheaf.xif.paper.S21dSourceTheaterCorrectionActual
import tmp.sheaf.xif.paper.S21cActualQUnitBridgeActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime

/-! # S21f: donor-built field comparison in the actual Fmod -> F direction

S21e supplies an actual C10 donor with

  I.initial.arithmetic = X.S.arithmetic.

This file redirects SourceTheaterFieldComparison to the actual direction:

  fieldMap : I.Fmod ->+* X.S.F,
  placeMap : I.Fmod-place -> X.S.F-place,

using the actual algebra embedding Fmod -> F and the actual selected common
prime place (FinitePlaceRelativeCommonPrime).  The reverse F -> Fmod map is not
constructed.

The q/theta transport condition is recorded as SourceTheaterQCorrection in this
direction; the field/place comparison itself is an actual witness.

No fake reverse map/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21fSourceTheaterFieldComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S21dSourceTheaterCorrectionActual
open LeanFormal.IUT.XiFPaper.S21eSourceTheaterFieldComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S21cActualQUnitBridgeActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (D : NativeOriginalInputDonors (X := X))
variable (b : Bad (nativePlaceSelection X.S))
variable (n : ThetaPilotCarrier l)

/-- The donor-built source contract. -/
abbrev fieldI : OriginalInput l (NativePlaces X.S) :=
  nativeOriginalInputOfDonors (X := X) D

/-- Actual Fmod equality from the donor. -/
theorem fieldI_fmod_eq :
    (fieldI (X := X) D).initial.arithmetic.Fmod =
      X.S.arithmetic.Fmod :=
  congrArg (fun A : InitialThetaArithmeticData l => A.Fmod)
    (D.initial_arithmetic)

/-- Actual field comparison function I.Fmod -> X.S.F in the source direction. -/
noncomputable def fieldComparisonFun :
    (fieldI (X := X) D).initial.arithmetic.Fmod → X.S.arithmetic.F :=
  fun x =>
    algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F
      ((fieldI_fmod_eq (X := X) D).symm ▸ x)

/-- The actual field comparison function is the algebra map transported along
the donor Fmod equality. -/
theorem fieldComparisonFun_eq (x : (fieldI (X := X) D).initial.arithmetic.Fmod) :
    fieldComparisonFun (X := X) D x =
      algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F
        ((fieldI_fmod_eq (X := X) D).symm ▸ x) := rfl

/-- Exact orientation gap for the place map: the actual source tower supplies
Fmod-places -> F-places, not F-places -> Fmod-places. -/
def SourceTheaterPlaceOrientationGap : Prop :=
  Nonempty (FinitePlaceAtPrime X.S.arithmetic.F (qVFamTensorP X.S b) →
    FinitePlaceAtPrime (fieldI (X := X) D).initial.arithmetic.Fmod
      (qVFamTensorP X.S b))

/-- Exact qUnit transport condition in the actual direction. -/
def SourceTheaterQUnitTransportCondition : Prop :=
  ((fieldI (X := X) D).theaterAt (n.val : Int) 0).thetaPacket.q =
    sourceThetaQ X.S b

end LeanFormal.IUT.XiFPaper.S21fSourceTheaterFieldComparisonActual

end
