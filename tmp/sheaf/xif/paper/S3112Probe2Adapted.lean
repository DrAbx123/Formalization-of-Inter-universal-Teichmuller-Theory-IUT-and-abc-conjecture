import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.S2757SourceCompletionNativeActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
noncomputable section
variable (X : N8NativeInput fiveLabel)
example (hA : X.S.arithmetic = S2753A) :
    nativeFPlaceOverBad X = nativeBadBasePlace X := by
  rw [hA]
  rw [← nativeFPlaceOverBad_comap X]
  rfl
