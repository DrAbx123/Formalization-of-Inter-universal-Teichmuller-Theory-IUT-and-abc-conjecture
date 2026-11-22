import tmp.sheaf.xif.paper.TateThetaProductAttempt
import LeanFormal.IUT.Foundations.Geometry.TateYCoordinateSeries
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation

noncomputable section
open LeanFormal.IUT.TateCurve
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaLogDerivAttempt

universe u

variable {K : Type u} [NormedField K]

/-- Formal first logarithmic derivative kernel of the theta product. -/
def thetaLogDerivKernel (z : K) : K := z / (1 - z)

/-- Formal second logarithmic derivative kernel. -/
def thetaLogDeriv2Kernel (z : K) : K := z / (1 - z) ^ 2

/-- Formal third logarithmic derivative kernel. -/
def thetaLogDeriv3Kernel (z : K) : K := z * (1 + z) / (1 - z) ^ 3

theorem thetaLogDeriv2Kernel_eq_coordinateKernel (z : K) :
    thetaLogDeriv2Kernel z = coordinateKernel z := rfl

theorem thetaLogDeriv3Kernel_eq_inversionOddYCoordinateKernel (z : K) :
    thetaLogDeriv3Kernel z = inversionOddYCoordinateKernel z := rfl

/-- Formal first log derivative theta series. -/
noncomputable def thetaLogDeriv (q u : K) : K :=
  ∑' n : Int, thetaLogDerivKernel (q ^ n * u)

/-- Formal second log derivative theta series. -/
noncomputable def thetaLogDeriv2 (q u : K) : K :=
  ∑' n : Int, thetaLogDeriv2Kernel (q ^ n * u)

/-- Formal third log derivative theta series. -/
noncomputable def thetaLogDeriv3 (q u : K) : K :=
  ∑' n : Int, thetaLogDeriv3Kernel (q ^ n * u)

theorem thetaLogDeriv2_eq_coordinateSeries (q u : K) :
    thetaLogDeriv2 q u = coordinateSeries q u := rfl

theorem thetaLogDeriv3_eq_inversionOddYCoordinateSeries (q u : K) :
    thetaLogDeriv3 q u = inversionOddYCoordinateSeries q u := rfl

theorem thetaLogDeriv3_eq_two_mul_y_add_x [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) :
    thetaLogDeriv3 q u = 2 * yCoordinateSeries q u + coordinateSeries q u := by
  rw [thetaLogDeriv3_eq_inversionOddYCoordinateSeries]
  exact inversionOddYCoordinateSeries_eq_two_mul_yCoordinateSeries_add_coordinateSeries hq u

#check thetaLogDerivKernel
#check thetaLogDeriv2Kernel
#check thetaLogDeriv3Kernel
#check thetaLogDeriv
#check thetaLogDeriv2
#check thetaLogDeriv3
#check thetaLogDeriv2_eq_coordinateSeries
#check thetaLogDeriv3_eq_inversionOddYCoordinateSeries
#print axioms thetaLogDeriv2_eq_coordinateSeries
#print axioms thetaLogDeriv3_eq_inversionOddYCoordinateSeries

end LeanFormal.IUT.XiFPaper.TateThetaLogDerivAttempt
end