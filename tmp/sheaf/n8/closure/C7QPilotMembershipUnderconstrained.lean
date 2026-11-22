import tmp.sheaf.n8.closure.C7HullPackagePaperRoute
import tmp.sheaf.n8.closure.C7Reductions
import Mathlib

/-!
# C7 qPilot membership underconstrained

The frozen C3 fields constrain tensorLanding only by tensorLanding_q.  Since
qPilotPoint = C3.tensorUnit, QPilotHullMembershipDonor is exactly the membership
of C3.tensorUnit in the canonical hull.  No frozen field forces that membership:
tensorUnit is an arbitrary unit and tensorLanding_q only fixes the q landing.

Consequently qPilot membership must remain an explicit exact subitem of the
paper-route target; it is not a derivable frozen-field fact.  No new tensorUnit
search is performed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7QPilotMembershipUnderconstrained

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7Reductions
open LeanFormal.IUT.N8Closure.C7HullPackagePaperRoute

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]

/-- qPilot membership is exactly tensorUnit membership in the canonical hull. -/
theorem qPilotMembership_iff_tensorUnit_mem :
    QPilotHullMembershipDonor (C3 := C3) ↔
      (C3.tensorUnit : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple :=
  qPilot_mem_canonicalHull_iff_tensorUnit_mem (C3 := C3)

/-- The frozen landing equation reduces qPilot membership to the q tensor
landing, not to any forced canonical-hull fact. -/
theorem qPilotMembership_iff_tensorLanding_q_mem :
    QPilotHullMembershipDonor (C3 := C3) ↔
      C3.tensorLanding (C3.q.q : CommonPrimeCompletion
        (K := I.initial.arithmetic.Fmod) C3.place) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  rw [qPilotMembership_iff_tensorUnit_mem]
  rw [← C3.tensorLanding_q]

/-- Exact subitem retained by the paper route. -/
theorem qPilotMembership_is_exact_subitem :
    C7QPilotSubitem (C3 := C3) ↔
      QPilotHullMembershipDonor (C3 := C3) :=
  Iff.rfl

end LeanFormal.IUT.N8Closure.C7QPilotMembershipUnderconstrained
