import tmp.sheaf.n8.closure.C9P6Closure
import tmp.sheaf.n8.closure.C3OverFConsumerCorrection
import Mathlib

/-!
# Wave21: paper P6 source closure over F

This file replaces the frozen Fmod tensor field of C9P6Closure.P6SourceClosure
by the actual zero-sorry OverFCorrectedC3Consumer.

The corrected closure copies all non-tensor components from the frozen P6
closure and installs the over-F C3 consumer as its tensor component.  The
frozen P6TensorLandingData field is not used in the corrected closure and no
adapter from over-F to Fmod is introduced.

The construction is actual as soon as the frozen P6 closure's other components
exist.  Those components are supplied by the frozen P6 closure argument; their
own source existence remains the pre-existing C9 named gap, not a new one.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperP6SourceClosureOverF

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C3OverFConsumerCorrection
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.P6Tensor
open LeanFormal.IUT.N8Closure.C3KummerActual
open LeanFormal.IUT.N8Closure.C9P6Closure
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6ChainB
open LeanFormal.IUT.N8Closure.P6Hull
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6SHEInd
open LeanFormal.IUT.N8Closure.P6Indices
open LeanFormal.IUT.N8Closure.P6Comparison
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL uG uI uVp

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (X : N8NativeInput l)
variable (T : TupleIndex X)
variable (Dq : NativeQDonor X)
variable (Lt : P6Tensor.P6TensorLandingData X)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]

/-- Corrected paper P6 source closure: same components as P6SourceClosure, with
the frozen Fmod tensor field replaced by the actual over-F consumer. -/
structure OverFP6SourceClosure
    (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (X : N8NativeInput l) (T : TupleIndex X)
    (Dq : NativeQDonor X)
    [hNorm : ∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [hMeas : ∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [hBorel : ∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [hHaar : ∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  chainA : P6ChainAData X
  chainB : CompleteAlpha (D := D)
  hull : P6HullSetup.{uv, uI}
  readout : P6Readout (X := X) (mu := mu)
  sheInd : P6FullData I C1 C2 C3 D
  /-- Corrected over-F C3 tensor consumer. -/
  tensor : OverFCorrectedC3Consumer X
  alphaIndex : AlphaIndex X T
  comparison : P6Exact X chainA.Q ∨ P6Epsilon X chainA.Q
  sourceExists : Nonempty (SourceAllowedOutput X)

/-- Actual corrected closure from the non-tensor components: the over-F
consumer is installed as the tensor field. -/
noncomputable def overFP6SourceClosureOfParts
    (chainA : P6ChainAData X)
    (chainB : CompleteAlpha (D := D))
    (hull : P6HullSetup.{uv, uI})
    (readout : P6Readout (X := X) (mu := mu))
    (sheInd : P6FullData I C1 C2 C3 D)
    (alphaIndex : AlphaIndex X T)
    (comparison : P6Exact X chainA.Q ∨ P6Epsilon X chainA.Q)
    (sourceExists : Nonempty (SourceAllowedOutput X)) :
    OverFP6SourceClosure D C1 C2 C3 X T Dq mu where
  chainA := chainA
  chainB := chainB
  hull := hull
  readout := readout
  sheInd := sheInd
  tensor := overFCorrectedC3Consumer X
  alphaIndex := alphaIndex
  comparison := comparison
  sourceExists := sourceExists

/-- The corrected tensor component is the actual over-F consumer. -/
theorem overFP6SourceClosureOfParts_tensor
    (chainA : P6ChainAData X)
    (chainB : CompleteAlpha (D := D))
    (hull : P6HullSetup.{uv, uI})
    (readout : P6Readout (X := X) (mu := mu))
    (sheInd : P6FullData I C1 C2 C3 D)
    (alphaIndex : AlphaIndex X T)
    (comparison : P6Exact X chainA.Q ∨ P6Epsilon X chainA.Q)
    (sourceExists : Nonempty (SourceAllowedOutput X)) :
    (overFP6SourceClosureOfParts (l := l) (V := V) D C1 C2 C3 X T Dq mu
      chainA chainB hull readout sheInd alphaIndex comparison sourceExists).tensor =
      overFCorrectedC3Consumer X :=
  rfl

/-- Corrected C3 complete source object: the frozen Fmod tensor field is
replaced by the actual over-F C3 consumer. -/
structure OverFC3CompleteSourceObject
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (X : N8NativeInput l) where
  c3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I
  q : NativeQDonor X
  action : NativeKummerAction.{0} X q
  tensor : OverFCorrectedC3Consumer X

/-- Actual corrected C3 object from explicit C3/native components. -/
noncomputable def overFC3CompleteSourceObjectOfParts
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, 0, 0} (l := l) (V := V) I)
    (Dq : NativeQDonor X) (A : NativeKummerAction.{0} X Dq) :
    OverFC3CompleteSourceObject I X where
  c3 := C3
  q := Dq
  action := A
  tensor := overFCorrectedC3Consumer X

end LeanFormal.IUT.N8Closure.PaperP6SourceClosureOverF
