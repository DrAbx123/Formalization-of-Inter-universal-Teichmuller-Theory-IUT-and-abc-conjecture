import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
noncomputable section
variable {l : PrimeGeFive} (X : N8NativeInput l)
example : nativeFPlaceOverBad X = nativeBadBasePlace X := by
  rw [← nativeFPlaceOverBad_comap X]
  rfl
