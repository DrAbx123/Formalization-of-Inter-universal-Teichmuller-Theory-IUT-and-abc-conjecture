import tmp.sheaf.n8.closure.EtaDistribHaarCharNormFormulaActual3
import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure

/-!
# EtaDistribHaarCharNormFormulaUnified

One-abbrev attempt at the char norm formula.  Actual `charUnit` packaging
is included.  Exact obstruction: `DistribHaarCharNormFormula` is stated with
the closure-file `Kf`, while `QDecomposition` is stated with the
general-scaling `Kf`; although definitionally equal, rewriting
`q = u • π^z` inside the dependent decomposition `D.z` produces a motive
that Lean rejects.  Additionally the exponent `d : ℕ` on the left is not
syntactically a `ℤ` exponent for `zpow_mul` until rewritten via
`zpow_natCast`.  No arbitrary conversion or extra abbrev is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaUnified

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Q := EtaGeneralQHaarScalingActual.Kf X

noncomputable def charUnit : (Q X)ˣ →* (NNReal)ˣ where
  toFun q := Units.mk0 (distribHaarChar (Q X) q)
    (ne_of_gt (distribHaarChar_pos))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [map_mul]

theorem charUnit_coe (q : (Q X)ˣ) :
    (charUnit X q : NNReal) = distribHaarChar (Q X) q := rfl

end LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaUnified