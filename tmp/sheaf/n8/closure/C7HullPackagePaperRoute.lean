import tmp.sheaf.n8.closure.C7ThetaMembershipDecisive
import tmp.sheaf.n8.closure.C7UToIQProof
import tmp.sheaf.n8.closure.C7Reductions
import Mathlib

/-!
# C7 hull package paper route

This file connects the decided C7 target to the paper/P6 route at the C7 layer.
The exact inputs are:

* C7ThetaSubitem : ThetaImageContainmentDonor C3 T n;
* C7QPilotSubitem : QPilotHullMembershipDonor C3.

The first is the corrected theta target; the second is the actual q-pilot
canonical-hull membership.  No tensorUnit search is performed here.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7HullPackagePaperRoute

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
open LeanFormal.IUT.N8Closure.C7ThetaMembershipDecisive
open LeanFormal.IUT.N8Closure.C7Reductions

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

/-- Exact C7 theta subitem. -/
def C7ThetaSubitem : Prop :=
  ThetaImageContainmentDonor (C3 := C3) T n

/-- Exact C7 q-pilot subitem. -/
def C7QPilotSubitem : Prop :=
  QPilotHullMembershipDonor (C3 := C3)

/-- The two exact paper-route C7 inputs. -/
structure C7PaperRouteInputs where
  theta : C7ThetaSubitem (C3 := C3) T n
  qPilot : C7QPilotSubitem (C3 := C3)

/-- The paper-route C7 hull package from the two exact inputs. -/
theorem paperRouteC7Hull_nonempty
    (I : C7PaperRouteInputs (C3 := C3) T n) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
      (T := T) n) :=
  c7HullPackage_of_decidedTarget (C1 := C1) (C2 := C2) (C3 := C3)
    (D := D) (C5 := C5) (mu := mu) (T := T) (n := n)
    I.theta I.qPilot

/-- Exact q-pilot subitem is equivalent to tensorUnit canonical-hull membership
(reused from C7Reductions; no new tensorUnit search). -/
theorem c7QPilotSubitem_iff_tensorUnit_mem :
    C7QPilotSubitem (C3 := C3) ↔
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple :=
  qPilot_mem_canonicalHull_iff_tensorUnit_mem (C3 := C3)

end LeanFormal.IUT.N8Closure.C7HullPackagePaperRoute
