import tmp.sheaf.n8.closure.C4ActualOutputFromSource

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4NativeOutputActual

universe u ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C4ActualOutputFromSource
open ABCBridge.N8.C4Actual

variable (l : PrimeGeFive)
variable (T : SourceNativeInitialThetaData.{u} l)

/-! ## Actual native output slice -/

/- The corrected native target gives actual `placeFamily` and `pilot`.  The
old C4 `eval`/`U`/`witness` cannot be rebuilt here: they are defined through
`I.sourceThetaPilotPoint` on an `OriginalInput`, and native
`SourceNativeInitialThetaData` does not provide such an input or a theta
evaluation carrier.  This is the decisive no-go for writing eval/U/witness on
the native slice without inventing a carrier. -/
structure C4NativeOutputSlice
    (l : PrimeGeFive) (T : SourceNativeInitialThetaData.{u} l) where
  target : C4NativeTargetCorrection l T

noncomputable def nativeC4OutputSlice :
    C4NativeOutputSlice l T where
  target := nativeC4TargetCorrection l T

theorem nativeC4OutputSlice_nonempty :
    Nonempty (C4NativeOutputSlice l T) :=
  ⟨nativeC4OutputSlice l T⟩

/-! ## Decisive no-go for eval/U/witness -/

/- The exact missing data is an actual theta evaluation carrier and map on
`ThetaPilotCarrier l × SignedLabel l.value`; no such native field exists, and
the only production evaluation (`sourceThetaPilotPoint`) consumes an
`OriginalInput`.  We do not fabricate a carrier. -/
structure C4NativeEvalMissing (l : PrimeGeFive)
    (T : SourceNativeInitialThetaData.{u} l) where
  evalCarrier : Type u
  eval : ThetaPilotCarrier l → SignedLabel l.value → evalCarrier
  U : ThetaPilotCarrier l → evalCarrier → Set evalCarrier

end LeanFormal.IUT.N8Closure.C4NativeOutputActual
