import tmp.sheaf.n8.closure.EtaCharFormulaOfDecomposition

noncomputable section
namespace LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiationProbe
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

example (u : (Integers (Kf X))ˣ) (y : Kf X) : u • y = (u : Kf X) * y := by
  simp [Units.smul_def]

example (q : (Kf X)ˣ) : (q : Kf X) = ((qDecomposition X q).u : Kf X) * ((chosenPiK X : Kf X) ^ (qDecomposition X q).z) := by
  have h := (qDecomposition X q).q_eq
  simpa [Units.smul_def, chosenPiK] using h

end LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiationProbe
