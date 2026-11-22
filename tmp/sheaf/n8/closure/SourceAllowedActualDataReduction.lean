import tmp.sheaf.n8.closure.SourceAllowedOutputActualAttempt
import tmp.sheaf.n8.closure.T11Actual
import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.C2Actual
import tmp.sheaf.n8.closure.SourcePilotRegion

/-!
# SourceAllowedActualData reduction

Decomposes the previous SourceAllowedActualData package into exact subobligations:

- P6BridgeDonors actual donor package;
- C2 SourceLogKummerData;
- C3 SourcePilotRegionData;
- C4 SourceWitnessedOutputData;
- T11 SourceThetaIQInterface (actual from C3 via T11Actual.thetaIQInterfaceActual);
- C6 C6ActualIQData plus measurable/Borel/Haar data.

The bridge is still derived from donors; no free bridge or witness.  Actual
subitems are constructed; missing source data are theorem-level named
obligations.  No free package field is asserted.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.SourceAllowedActualDataReduction

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open ABCBridge.N8.T11Actual
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- Subobligation 1: actual P6 bridge donor package. -/
def P6BridgeObligation (X : N8NativeInput l) : Prop :=
  Nonempty (P6BridgeDonors X)

/-- Subobligation 2: C2 over the actual bridge input/binding. -/
def C2Obligation (D : P6BridgeDonors X) : Prop :=
  Nonempty (SourceLogKummerData (actualBridge D).input (actualBridge D).binding)

/-- Subobligation 3: C3 over the actual bridge input. -/
def C3Obligation (D : P6BridgeDonors X) : Prop :=
  Nonempty (SourcePilotRegionData.{0, 0, 0, 0, 0, 0, 0} (actualBridge D).input)

/-- Subobligation 4: C4 over the actual bridge input and paper label group. -/
def C4Obligation (D : P6BridgeDonors X) : Prop :=
  Nonempty (SourceWitnessedOutputData (actualBridge D).input
    (P6Comparison.PaperLabel l))

/-- Subobligation 5: T11 interface; actual from C3, no missing donor. -/
def T11Obligation (D : P6BridgeDonors X)
    (C3 : SourcePilotRegionData (actualBridge D).input) : Type _ :=
  SourceThetaIQInterface (I := (actualBridge D).input) C3

/-- Actual T11 interface construction. -/
def t11OfC3 (D : P6BridgeDonors X)
    (C3 : SourcePilotRegionData (actualBridge D).input) :
    T11Obligation D C3 :=
  thetaIQInterfaceActual (I := (actualBridge D).input) C3

/-- Subobligation 6: C6 IQ data plus its measurable/Haar data. -/
def C6Obligation (D : P6BridgeDonors X)
    (C3 : SourcePilotRegionData (actualBridge D).input)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : MeasureTheory.Measure
      (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [MeasureTheory.Measure.IsAddHaarMeasure mu] : Prop :=
  Nonempty (C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)

/-- Actual subobligation 1 from the P6Bridge named donor theorem. -/
theorem p6BridgeObligation_actual : P6BridgeObligation X :=
  P6Bridge.p6BridgeDonorsExist X

/-- Actual subobligation 2 from the C2 stage-2 existence theorem. -/
theorem c2Obligation_actual (D : P6BridgeDonors X) : C2Obligation D :=
  LeanFormal.IUT.N8Closure.C2Actual.sourceLogKummerData_nonempty_actual (actualBridge D).input (actualBridge D).binding

/-- Exact named missing subobligation 6: actual C6 IQ data over C3's tensor. -/
theorem c6Obligation_actual (D : P6BridgeDonors X)
    (C3 : SourcePilotRegionData (actualBridge D).input)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : MeasureTheory.Measure
      (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [MeasureTheory.Measure.IsAddHaarMeasure mu] : C6Obligation D C3 mu :=
  ⟨C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu⟩

/-- Explicit component builder: no free package field; all components are
separate arguments, T11 is actual, and the bridge is derived from donors. -/
def sourceAllowedActualDataOfComponents
    (D : P6BridgeDonors X)
    (C2 : SourceLogKummerData (actualBridge D).input (actualBridge D).binding)
    (C3 : SourcePilotRegionData (actualBridge D).input)
    (D4 : SourceWitnessedOutputData (actualBridge D).input
      (P6Comparison.PaperLabel l))
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : MeasureTheory.Measure
      (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu) :
    SourceAllowedActualData X where
  donors := D
  C2 := C2
  C3 := C3
  D := D4
  T := t11OfC3 D C3
  measurableSpace := inferInstance
  borelSpace := inferInstance
  mu := mu
  addHaar := inferInstance
  B := B

end LeanFormal.IUT.N8Closure.SourceAllowedActualDataReduction
