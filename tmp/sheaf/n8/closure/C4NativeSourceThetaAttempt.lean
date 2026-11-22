import tmp.sheaf.n8.closure.C4NativeEvalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4NativeSourceThetaAttempt

universe u ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C4NativeEvalActual

variable (l : PrimeGeFive)
variable (T : SourceNativeInitialThetaData.{u} l)

/-! ## Production search result -/

/- The production eval is `sourceThetaPilotPoint` in
`Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:201`.  Its signature
requires `(I : OriginalInput l V)`, `(v : V)`, and
`(R : I.SourceImageRealization v)`.  `SourceNativeInitialThetaData` has none
of those fields and no native theta-eval declaration exists.  The exact
missing production declaration is a native
`SourceNativeInitialThetaData -> thetaPilotPoint` eval (or native
`SourceImageRealization` plus `thetaImageValue`). -/

structure NativeThetaEvalProductionInput (l : PrimeGeFive)
    (T : SourceNativeInitialThetaData.{u} l) where
  V : Type uv
  I : OriginalInput.{ua, uv, upi, umon, ui} l V
  v : V
  R : I.SourceImageRealization v

noncomputable def nativeEvalFromProductionInput
    (X : NativeThetaEvalProductionInput (l := l) (T := T)) :
    C4NativeEvalActual (l := l) X.V X.I :=
  c4NativeEvalActualOfSource (l := l) X.I X.v X.R

theorem nativeEvalFromProductionInput_eval
    (X : NativeThetaEvalProductionInput (l := l) (T := T))
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    (nativeEvalFromProductionInput (l := l) (T := T) X).eval n j =
      X.I.sourceThetaPilotPoint X.v X.R n j :=
  rfl

/-! ## Exact gap decomposition -/

end LeanFormal.IUT.N8Closure.C4NativeSourceThetaAttempt
