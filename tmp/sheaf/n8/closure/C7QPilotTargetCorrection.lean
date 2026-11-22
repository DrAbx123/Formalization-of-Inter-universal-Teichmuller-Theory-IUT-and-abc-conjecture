import tmp.sheaf.n8.closure.C7QPilotMembershipUnderconstrained
import tmp.sheaf.n8.closure.C7HullPackagePaperRoute
import Mathlib

/-!
# C7 qPilot target correction

The frozen C3 fields do not force QPilotHullMembershipDonor: by
qPilotMembership_iff_tensorUnit_mem it is exactly the membership of the
arbitrary tensorUnit in the canonical hull.  The corrected target therefore
carries qPilot membership as an explicit source subitem (C7PaperRouteInputs),
not as a derived frozen-field fact and not as a free membership field of the
hull package.

This file records the corrected target and the corrected consumer.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7QPilotTargetCorrection

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
open LeanFormal.IUT.N8Closure.C7HullPackagePaperRoute
open LeanFormal.IUT.N8Closure.C7QPilotMembershipUnderconstrained

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

/-- Corrected target: theta containment plus qPilot membership as explicit
source inputs, not as a derived frozen-field fact. -/
def C7QPTargetCorrected : Prop :=
  Nonempty (C7PaperRouteInputs (C3 := C3) T n)

/-- The corrected target is exactly the two paper-route subitems. -/
theorem c7QPTargetCorrected_iff_inputs :
    C7QPTargetCorrected (C3 := C3) T n ↔
      Nonempty (C7PaperRouteInputs (C3 := C3) T n) :=
  Iff.rfl

/-- The corrected target still exposes qPilot membership as an explicit
subitem (no free membership). -/
theorem c7QPTargetCorrected_qPilot
    (h : C7QPTargetCorrected (C3 := C3) T n) :
    C7QPilotSubitem (C3 := C3) := by
  obtain ⟨I⟩ := h
  exact I.qPilot

/-- Corrected consumer: the C7 hull package is consumed from the explicit
paper-route inputs, not from a claimed derivation of qPilot membership. -/
theorem c7QPTargetCorrected_hullPackage
    (I : C7PaperRouteInputs (C3 := C3) T n) :
    Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
      (T := T) n) :=
  paperRouteC7Hull_nonempty (C1 := C1) (C2 := C2) (C3 := C3)
    (D := D) (C5 := C5) (mu := mu) (T := T) (n := n) I

/-- Target correction theorem: qPilot membership is an input subitem, not a
conclusion of the frozen C3 fields. -/
theorem c7QPTargetCorrection :
    C7QPTargetCorrected (C3 := C3) T n →
      C7QPilotSubitem (C3 := C3) :=
  fun h => c7QPTargetCorrected_qPilot (C3 := C3) (T := T) (n := n) h

end LeanFormal.IUT.N8Closure.C7QPilotTargetCorrection
