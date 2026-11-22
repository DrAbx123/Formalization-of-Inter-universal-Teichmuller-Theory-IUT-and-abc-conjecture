import tmp.sheaf.n8.closure.TargetSignature
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.LabelData
import tmp.sheaf.n8.closure.IPLFamilyData
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.SourceThetaToIQ
import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.SourceDegreeComparisonIQ
import tmp.sheaf.n8.closure.SourcePilotApproximationIQ

/-!
# N8 C10 actual-IQ closure

N8FullOutput uses the actual C1-C5 data, T10 IPLFamilyData, C6ActualIQData,
the actual C7 IQ hull family, C8IQ sourceDegreeComparisonIQ and C9IQ
sourcePilotApproximationIQ_stage2. The C0 output is used only for the base
field and is supplied by C0 n8_targetOutput_nonempty. No total-goal sorry and
no old C6ProductVolumeData/Core-only IPL proxy is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C10Full

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.LabelData
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.C8IQ
open LeanFormal.IUT.N8Closure.C9IQ

universe ua uv upi umon ui uL uG uA uW u_1

variable {l : PrimeGeFive} {V : Type uv}

/-- N8 actual-IQ full output. All C1-C9 slots are actual declared interfaces;
the only C0 obligation is the base target. -/
structure N8FullOutput
    (A : C0ProductionAdditiveIndex.{ua})
    (L : LabelData.{uL})
    (transport : C0AdditiveLabelTransport A L)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C3P : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I)
    (O : N8TargetOutput (l := l) (V := V) (Label := A.Index) (Choice := Unit) ⟨I⟩) where
  /-- C0 base target; supplied only by C0 n8_targetOutput_nonempty. -/
  base : N8TargetOutput (l := l) (V := V) (Label := A.Index) (Choice := Unit) ⟨I⟩ := O
  /-- C1 actual source binding. -/
  fieldC1 : SourceInputBinding I
  /-- C2 actual local log-Kummer data. -/
  fieldC2 : SourceLogKummerData I fieldC1
  /-- C3 actual source pilot region. -/
  fieldC3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I := C3P
  /-- T11 actual source theta -> IQ interface. -/
  fieldT : SourceThetaIQInterface (I := I) C3P
  /-- C4 actual witnessed output over the paper permutation-label group. -/
  fieldC4 : SourceWitnessedOutputData (l := l) (V := V) I
    (Multiplicative (Additive (Equiv.Perm L.Labels)))
  /-- T10 actual FPrimeStrip poly-iso family. -/
  iplFamily : IPLFamilyData I
  /-- C5 actual algorithm compatibility over Additive G. -/
  fieldC5 : SourceAlgorithmCompatibilityData
    (LAdd := Additive (Equiv.Perm L.Labels)) I fieldC1 fieldC2 C3P fieldC4
  /-- Measurability on the C3 tensor carrier. -/
  [measurableSpace : MeasurableSpace
    (ArithmeticTensorTupleBlock C3P.tensorPlaces C3P.tensorTuple)]
  /-- Borel structure on the C3 tensor carrier. -/
  [borelSpace : BorelSpace
    (ArithmeticTensorTupleBlock C3P.tensorPlaces C3P.tensorTuple)]
  /-- C6 actual Haar measure on the C3 tensor carrier. -/
  fieldMu : Measure (ArithmeticTensorTupleBlock C3P.tensorPlaces C3P.tensorTuple)
  /-- C6 actual Haar measure instance. -/
  [addHaar : Measure.IsAddHaarMeasure fieldMu]
  /-- C6 actual IQ data. -/
  fieldC6 : C6ActualIQData C3P.tensorPlaces C3P.tensorTuple fieldMu
  /-- C7 actual IQ hull family. -/
  fieldC7 : ∀ n : ThetaPilotCarrier l,
    SourceHolomorphicHullData (C1 := fieldC1) (C2 := fieldC2) (C3 := C3P)
      (D := fieldC4) (C5 := fieldC5) (mu := fieldMu) (B := fieldC6) (T := fieldT) n
  /-- C8IQ actual degree/mu_log comparison for every C7 witness. -/
  fieldC8 : ∀ n : ThetaPilotCarrier l,
    iqDegree (C3 := C3P) (mu := fieldMu) fieldC6 =
      fieldC6.normalizationWeight *
        (fieldC6.signedHullLog - fieldC6.unitReferenceLog)
  /-- C9IQ actual values bound and q-approximation. -/
  fieldC9 :
    actual_values_bounded (C3 := C3P) (mu := fieldMu) (B := fieldC6)
        (T := fieldT) (C7 := fieldC7) ∧
      actual_q_approximated (C3 := C3P) (mu := fieldMu) (B := fieldC6)
        (T := fieldT) (C7 := fieldC7)

/-- T11 chosen actual theta/IQ interface from the named-sorry obligation. -/
noncomputable def thetaT
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I) :
    SourceThetaIQInterface (I := I) C3 :=
  Classical.choice (sourceThetaIQObligation C3)

/-- C0 base output; the only C0 named-sorry call. -/
noncomputable def c0Base
    (A : C0ProductionAdditiveIndex.{ua})
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    N8TargetOutput (l := l) (V := V) (Label := A.Index) (Choice := Unit) ⟨I⟩ :=
  Classical.choice (n8_targetOutput_nonempty (l := l) (V := V)
    (Label := A.Index) (Choice := Unit) ⟨I⟩)

/-- C10 actual-IQ assembly. The structure is actually constructed from the
explicit C1-C9 data; C0 is called only for the base field. -/
theorem n8Assembly_closure
    (A : C0ProductionAdditiveIndex.{ua})
    (L : LabelData.{uL})
    (transport : C0AdditiveLabelTransport A L)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I
      (Multiplicative (Additive (Equiv.Perm L.Labels))))
    (IPL : IPLFamilyData I)
    (C5 : SourceAlgorithmCompatibilityData
      (LAdd := Additive (Equiv.Perm L.Labels)) I C1 C2 C3 C4)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure mu]
    (C7 : ∀ n : ThetaPilotCarrier l,
      SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
        (D := C4) (C5 := C5) (mu := mu)
        (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) (T := thetaT C3) n)
    :
    Nonempty (N8FullOutput A L transport I C3 (c0Base A I)) := by
  let base := c0Base A I
  let C6 := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu
  exact ⟨{
    base := base
    fieldC1 := C1
    fieldC2 := C2
    fieldC3 := C3
    fieldT := thetaT C3
    fieldC4 := C4
    iplFamily := IPL
    fieldC5 := C5
    fieldMu := mu
    fieldC6 := C6
    fieldC7 := C7
    fieldC8 := fun n => sourceDegreeComparisonIQ C1 C2 C3 C4 C5 mu (T := thetaT C3) n (C7 n)
    fieldC9 := sourcePilotApproximationIQ_stage2 C1 C2 C3 C4 C5 mu (B := C6) (T := thetaT C3) C7
  }⟩

end LeanFormal.IUT.N8Closure.C10Full
