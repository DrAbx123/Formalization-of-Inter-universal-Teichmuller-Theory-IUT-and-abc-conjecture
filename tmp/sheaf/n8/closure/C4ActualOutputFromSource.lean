import tmp.sheaf.n8.closure.SourceWitnessedOutput
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4ActualOutputFromSource

universe u ua uv upi umon ui uL

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open ABCBridge.N8.C4Actual

/-! ## Native C4 target correction -/

/- The old C4 target is indexed by an arbitrary `OriginalInput`.  The actual
native Definition 3.1 data `SourceNativeInitialThetaData` supplies the actual
place family `tuple.V` and the actual theta-pilot carrier; this is the
corrected target slice. -/

structure C4NativeTargetCorrection (l : PrimeGeFive)
    (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{u} l) where
  /-- Actual native finite-place family. -/
  placeFamily : Set (NumberFieldPlace T.arithmetic.K)
  /-- Actual theta-pilot carrier data. -/
  pilot : C3ThetaPilotData l

noncomputable def nativeC4TargetCorrection (l : PrimeGeFive)
    (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{u} l) :
    C4NativeTargetCorrection l T where
  placeFamily := T.tuple.V
  pilot := { n := ⟨0, Nat.succ_pos (lStar l.value)⟩ }

theorem nativeC4TargetCorrection_nonempty (l : PrimeGeFive)
    (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{u} l) :
    Nonempty (C4NativeTargetCorrection l T) :=
  ⟨nativeC4TargetCorrection l T⟩

/-! The old C4 target is indexed by an arbitrary `OriginalInput`; native
`SourceNativeInitialThetaData` supplies no such field.  This is the exact target
correction: the native slice above uses `tuple.V` and the actual theta-pilot
carrier, while the old C4 target is not rebuilt from native data. -/

end LeanFormal.IUT.N8Closure.C4ActualOutputFromSource
