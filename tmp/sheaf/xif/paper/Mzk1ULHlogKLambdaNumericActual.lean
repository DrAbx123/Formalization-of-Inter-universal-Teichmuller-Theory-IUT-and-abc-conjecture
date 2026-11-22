/- hlogK λ 数值界（B 表）：F 版 hlogK + 组装成 HlogKLambdaData（加 21 为 +21 版形状）。
  donor: Mzk1G1HlogKAssemblyActual.hlogK_of_relative_different_bound（DONE 23:08:51）;
  Mzk1ULHlogKHSULambdaStatementsActual.HlogKLambdaData（DONE 10:03:26）;
  Mzk1ULSerreWildBoundActual.differentExponent_lt_of_not_pow_dvd（DONE 00:57:23，wild 端）。 -/
import tmp.sheaf.xif.paper.Mzk1G1HlogKAssemblyActual
import tmp.sheaf.xif.paper.Mzk1ULBadFPrimeSetActual
import tmp.sheaf.xif.paper.Mzk1ULHlogKHSULambdaStatementsActual
import tmp.sheaf.xif.paper.Mzk1ULSerreWildBoundActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHlogKLambdaNumericActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1HlogKAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hlogK F 版（相对不同上界 ⇒ log dK ≤ log dF+log fF+2log l）。 -/
theorem hlogK_F_of_relative_bound
    (hbound : Real.log
        ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.F) (𝓞 T.arithmetic.K)) : ℕ) : ℝ) ≤
      (Module.finrank ℚ T.arithmetic.K : ℝ) *
        (logConductorFActual T + 2 * Real.log (l.value : ℝ))) :
    Real.log (NumberField.rootDiscr T.arithmetic.K) ≤
      Real.log (NumberField.rootDiscr T.arithmetic.F) +
        logConductorFActual T + 2 * Real.log (l.value : ℝ) :=
  Mzk1G1HlogKAssemblyActual.hlogK_of_relative_different_bound (T := T) hbound

/-- hlogK λ 形状（+21 版，ι=Unit 单分量）: log dK ≤ S_ar+2log l+21。 -/
theorem hlogdK_lambda_data
    (hbound : Real.log
        ((Ideal.absNorm (differentIdeal (𝓞 T.arithmetic.F) (𝓞 T.arithmetic.K)) : ℕ) : ℝ) ≤
      (Module.finrank ℚ T.arithmetic.K : ℝ) *
        (logConductorFActual T + 2 * Real.log (l.value : ℝ))) :
    Mzk1ULHlogKHSULambdaStatementsActual.HlogKLambdaData Unit := by
  have h := hlogK_F_of_relative_bound (l := l) T hbound
  refine
    { w := fun _ => 1
      D := fun _ => Real.log (NumberField.rootDiscr T.arithmetic.K)
      S_ar := Real.log (NumberField.rootDiscr T.arithmetic.F) + logConductorFActual T
      logl := (l.value : ℝ)
      hlogdK := ?_ }
  simpa using (le_trans h (by linarith))

#print axioms hlogK_F_of_relative_bound
#print axioms hlogdK_lambda_data

end LeanFormal.IUT.XiFPaper.Mzk1ULHlogKLambdaNumericActual