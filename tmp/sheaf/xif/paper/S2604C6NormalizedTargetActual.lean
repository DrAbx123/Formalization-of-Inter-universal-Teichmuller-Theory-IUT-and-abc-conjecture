import tmp.sheaf.n8.closure.SourceThetaToIQ
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2604C6NormalizedTargetActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [MeasurableSpace (IQCarrier C3)]
variable [BorelSpace (IQCarrier C3)]
variable (mu : Measure (IQCarrier C3))
variable [Measure.IsAddHaarMeasure mu]
variable (n : ThetaPilotCarrier l)
variable (j : Nat -> Nat -> Nat -> SignedLabel l.value)

/-- Actual C6 IQ data, with the Real-valued `normalizedLogVolume` (NOT the
Haar `iqInterface.logVolume`). -/
noncomputable def C6NormData : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu :=
  C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu

/-- Actual theta image interface. -/
noncomputable def C6NormT : SourceThetaIQInterface (I := I) C3 :=
  thetaIQInterfaceOfQUnit (I := I) C3

/-- The actual Real unit region of the C6 IQ carrier. -/
noncomputable def C6UnitRegion : Set (IQCarrier C3) :=
  arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple

/-- The actual theta-image point at `(a,b,c)`. -/
noncomputable def C6Point (a b c : Nat) : IQCarrier C3 :=
  (C6NormT I C3).thetaImage n (j a b c)

/-- The actual comparison region: the Real unit region together with the
theta-image point.  This is a Set on the C6 carrier, not the Haar interface
region. -/
noncomputable def C6ComparisonRegion (a b c : Nat) : Set (IQCarrier C3) :=
  C6UnitRegion I C3 ∪ {C6Point I C3 n j a b c}

/-- **P4 on the actual C6 carrier, using the Real `normalizedLogVolume`.**
arithmeticWeight is bounded by the Real normalized log-volume of the actual
unit region plus theta-image point.  No Haar `logVolume`, no `toReal`, no raw
source theta point. -/
def P4C6NormalizedWeightTarget : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      (C6NormData I C3 mu).normalizedLogVolume (C6ComparisonRegion I C3 n j a b c)

/-- **P5 on the actual C6 carrier, using the Real `normalizedLogVolume`.**
The theta-image point volume is bounded by the canonical height. -/
def P5C6NormalizedHeightTarget : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (C6NormData I C3 mu).normalizedLogVolume
      {C6Point I C3 n j a b c} <=
      Height.logHeight₁ (abcRationalPoint a c)

/-- Exact identification: P4 uses `C6ActualIQData.normalizedLogVolume`, not
`iqInterface.logVolume`. -/
theorem P4C6NormalizedWeightTarget_eq :
    P4C6NormalizedWeightTarget I C3 mu n j =
      (forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          (C6NormData I C3 mu).normalizedLogVolume
            (C6UnitRegion I C3 ∪ {C6Point I C3 n j a b c})) := rfl

#print axioms P4C6NormalizedWeightTarget_eq

end LeanFormal.IUT.XiFPaper.S2604C6NormalizedTargetActual
end
