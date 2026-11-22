import tmp.sheaf.n8.closure.C7ThetaUnitHullFinal
import tmp.sheaf.n8.closure.C7Native
import Mathlib

/-!
# C7 theta membership decisive decision

The actual theta unit-reference membership is not derivable from the frozen
interfaces and is stronger than what C7 consumes.  C7's hull package needs only
theta-image containment (plus qPilot membership), and that corrected target is
sufficient for the actual hull closure.

This file therefore decides: use ThetaImageContainmentDonor as the C7 target;
the actual unit-reference membership is an optional stronger donor, not a
prerequisite.  No tensorUnit search is repeated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7ThetaMembershipDecisive

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7ThetaUnitHullFinal
open LeanFormal.IUT.N8Closure.C7ThetaContainmentAttempt

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 D)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- The corrected C7 target: theta-image containment in the actual IQ hull. -/
def C7DecidedTarget : Prop :=
  ThetaImageContainmentDonor (C3 := C3) T n

/-- The stronger actual unit-reference membership implies the decided target. -/
theorem c7DecidedTarget_of_actualThetaUnitMembership
    (h : ActualThetaUnitMembership (C3 := C3) n) :
    C7DecidedTarget (C3 := C3) (actualThetaInterface (I := I) C3) n := by
  unfold C7DecidedTarget
  let hdonor : ThetaUnitHullDonor (C3 := C3) (T := actualThetaInterface (I := I) C3) n :=
    ⟨h, LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt.arithmeticTupleCanonicalUnitReference_subset_canonicalHull
      C3.tensorPlaces C3.tensorTuple⟩
  exact thetaImageContainmentDonor_of_unitDonor (C3 := C3) (T := actualThetaInterface (I := I) C3) (n := n) hdonor

/-- The decided target plus the actual q-pilot membership closes the C7 hull
package.  This is the decisive route: unit-reference membership is not needed. -/
theorem c7HullPackage_of_decidedTarget
    (hTheta : C7DecidedTarget (C3 := C3) T n)
    (hq : QPilotHullMembershipDonor (C3 := C3)) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
      (T := T) n) :=
  sourceHolomorphicHullData_nonempty_of_native (C1 := C1) (C2 := C2)
    (C3 := C3) (D := D) (C5 := C5) (mu := mu) (T := T) (n := n)
    hTheta hq

/-- Decisive target correction: the actual unit-reference membership is
sufficient but not required; the corrected target C7DecidedTarget is the one
used by the actual hull closure. -/
theorem c7_target_correction :
    ActualThetaUnitMembership (C3 := C3) n →
      C7DecidedTarget (C3 := C3) (actualThetaInterface (I := I) C3) n :=
  fun h => c7DecidedTarget_of_actualThetaUnitMembership (C3 := C3) (n := n) h

end LeanFormal.IUT.N8Closure.C7ThetaMembershipDecisive
