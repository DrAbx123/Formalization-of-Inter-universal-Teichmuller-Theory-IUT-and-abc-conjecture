import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.C6ActualIQData

/-!
# SourceAllowedOutput actual attempt

Constructs P6Comparison.SourceAllowedOutput X from actual data:

  P6BridgeDonors X
  -> exact old C1 bridge
  -> C2/C3/C4/T11 actual data
  -> C6 measurable/Haar/IQ data

The bridge and C4 witness are derived from donors and C4's zero label, not
stored as free fields.  C2/C3/C4/T11/C6 remain explicit actual-data fields; the
single missing package existence is the named sourceAllowedActualData_nonempty.

No free bridge or free witness is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- Exact old C1 bridge derived from the P6 donor package. -/
noncomputable def actualBridge (D : P6BridgeDonors X) : NativeOldC1Bridge X :=
  D.toNativeOldC1Bridge

/-- Actual data package needed to construct one SourceAllowedOutput.  Bridge is
not a field: it is derived from donors.  The C4 witness is not a field either;
it is derived below from the zero signed label. -/
structure SourceAllowedActualData (X : N8NativeInput l) where
  donors : P6BridgeDonors X
  C2 : SourceLogKummerData (actualBridge donors).input (actualBridge donors).binding
  C3 : SourcePilotRegionData (actualBridge donors).input
  D : SourceWitnessedOutputData (actualBridge donors).input
    (P6Comparison.PaperLabel l)
  T : SourceThetaIQInterface (I := (actualBridge donors).input) C3
  [measurableSpace : MeasurableSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [borelSpace : BorelSpace
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  mu : MeasureTheory.Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  [addHaar : MeasureTheory.Measure.IsAddHaarMeasure mu]
  B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu

/-- Actual construction of SourceAllowedOutput from the data package.  The
bridge is actualBridge donors; n is C4.pilot.n; x is the actual constant
theta-pilot point; w is the zero-label witness. -/
noncomputable def sourceAllowedOutputOfActualData
    (A : SourceAllowedActualData X) : P6Comparison.SourceAllowedOutput X :=
  let b := actualBridge A.donors
  let n : ThetaPilotCarrier l := A.D.pilot.n
  let x : b.input.ThetaPilotPoint A.D.place.v :=
    b.input.constantThetaPilotPoint A.D.place.v A.D.place.R 1
  let w : A.D.Witness n x :=
    ⟨zeroSignedLabel, ⟨A.D.eval n x zeroSignedLabel, rfl⟩⟩
  { bridge := b
    C2 := A.C2
    C3 := A.C3
    D := A.D
    T := A.T
    measurableSpace := A.measurableSpace
    borelSpace := A.borelSpace
    mu := A.mu
    addHaar := A.addHaar
    B := A.B
    n := n
    x := x
    w := w }

/-- Conditional actual nonempty: a data package yields an actual
SourceAllowedOutput. -/
theorem sourceAllowedOutput_nonempty_of_actualData
    (h : Nonempty (SourceAllowedActualData X)) :
    Nonempty (P6Comparison.SourceAllowedOutput X) := by
  obtain ⟨A⟩ := h
  exact ⟨sourceAllowedOutputOfActualData A⟩

/-- Exact minimal named gap: the actual P6BridgeDonors/C2/C3/C4/T11/C6 data
package is missing.  This is not a free bridge or witness. -/
theorem sourceAllowedActualData_nonempty :
    Nonempty (SourceAllowedActualData X) := by
  sorry

/-- Conditional reduction of the existing SourceAllowedOutput existence target
to the exact data-package gap. -/
theorem sourceAllowedOutput_nonempty_of_package :
    Nonempty (P6Comparison.SourceAllowedOutput X) :=
  sourceAllowedOutput_nonempty_of_actualData sourceAllowedActualData_nonempty

end LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
