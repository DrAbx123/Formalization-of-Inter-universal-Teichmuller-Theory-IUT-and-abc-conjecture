import tmp.sheaf.xif.paper.S2729GlobalPointMapActual
import tmp.sheaf.xif.paper.S2593TensorNormActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312CarrierRealizationSpec
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2729GlobalPointMapActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2732ProductFormulaCounterexampleActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Product-formula counterexample: if the global product of the per-b S2588
point norms at the actual ABC triple `(1,2,3)` is `1`, then its negative log
is `0`; but the arithmetic weight of `x = 1/3` is `log 6 ≠ 0`.  Hence the
global product norm cannot recover `arithmeticWeight` in this case. -/
theorem S2732_product_formula_counterexample
    (hprod : S2729GlobalPointNorm (l := l) T 1 2 3 = 1) :
    -Real.log (S2729GlobalPointNorm (l := l) T 1 2 3) = 0 ∧
      arithmeticWeight (abcRationalPoint 1 3) = Real.log 6 := by
  constructor
  · rw [hprod, Real.log_one]
    norm_num
  · exact cor312CarrierSpec_arithmeticWeight_abcRationalPoint_one_two_three

/-- Consequently, under the product-norm-one hypothesis, the product-formula
equality `-log globalNorm = arithmeticWeight` is false. -/
theorem S2732_no_product_formula_eq
    (hprod : S2729GlobalPointNorm (l := l) T 1 2 3 = 1) :
    (-Real.log (S2729GlobalPointNorm (l := l) T 1 2 3) ≠
      arithmeticWeight (abcRationalPoint 1 3)) := by
  have h := S2732_product_formula_counterexample T hprod
  rw [h.1, h.2]
  exact (Real.log_pos (by norm_num : (1 : Real) < 6)).ne

#check S2732_product_formula_counterexample
#print axioms S2732_no_product_formula_eq

end LeanFormal.IUT.XiFPaper.S2732ProductFormulaCounterexampleActual
end
