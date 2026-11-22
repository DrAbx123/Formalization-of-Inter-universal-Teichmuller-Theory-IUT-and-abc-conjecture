import tmp.sheaf.n8.closure.C4NativeEvalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4NativeThetaTargetCorrection

universe u ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C4NativeEvalActual

variable (l : PrimeGeFive)
variable (T : SourceNativeInitialThetaData.{u} l)

/-! ## Corrected native theta target -/

/- The corrected target makes the missing production input explicit: a type
`V`, an `OriginalInput l V`, a place `v`, and `I.SourceImageRealization v`.
The native theta eval is then the actual `I.sourceThetaPilotPoint`; no
carrier is invented. -/
structure C4NativeThetaTargetCorrection (l : PrimeGeFive)
    (T : SourceNativeInitialThetaData.{u} l) where
  V : Type uv
  I : OriginalInput.{ua, uv, upi, umon, ui} l V
  v : V
  R : I.SourceImageRealization v

noncomputable def correctedNativeEval
    (C : C4NativeThetaTargetCorrection l T) :
    C4NativeEvalActual (l := l) C.V C.I :=
  c4NativeEvalActualOfSource (l := l) C.I C.v C.R

theorem correctedNativeEval_eval
    (C : C4NativeThetaTargetCorrection l T)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    (correctedNativeEval (l := l) (T := T) C).eval n j =
      C.I.sourceThetaPilotPoint C.v C.R n j :=
  rfl

theorem C4NativeThetaTargetCorrection_hasProductionInput
    (C : C4NativeThetaTargetCorrection l T) :
    Nonempty (C.I.SourceImageRealization C.v) :=
  ⟨C.R⟩

/-! ## Exact named gap -/

/- Native `SourceNativeInitialThetaData` supplies no `V`/`I`/`v`/`R`; this
is the exact missing production input for the corrected target. -/
end LeanFormal.IUT.N8Closure.C4NativeThetaTargetCorrection
