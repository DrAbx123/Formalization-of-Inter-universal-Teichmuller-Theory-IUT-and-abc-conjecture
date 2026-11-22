import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure

/-!
# EtaDistribHaarCharNormFormulaAttempt

Attempt at `DistribHaarCharNormFormula` from the actual decomposition
`q = u • π^z`, `char(u)=1`, `char(π)=normπ^d`.

Exact obstruction: `distribHaarChar` is a `MonoidHom` into `ℝ≥0`, not a
monoid-with-zero hom, so the available `map_zpow` lemma does not directly
apply; one must first package its nonzero values as `(ℝ≥0)ˣ` and transport
the zpow coercion.  Second, `char(u)=1` uses the measure-dependent unit
invariance lemma, requiring a chosen Haar measure with positive finite mass
on `O`; that measure choice/positivity is not supplied by the current
unconditional decomposition.  No arbitrary conversion is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure
open LeanFormal.IUT.N8Closure.NativeC3
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

end LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaAttempt