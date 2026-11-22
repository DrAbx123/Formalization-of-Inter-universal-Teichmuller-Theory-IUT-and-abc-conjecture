import LeanFormal.IUT.IUTIV.Estimates.Section2
import Mathlib.NumberTheory.Chebyshev

noncomputable section
open Real Filter
namespace LeanFormal.IUT.XiFPaper.Mzk1S1PrimeAvoidanceActual
open LeanFormal.IUT.IUTIV.Estimates

structure S1PrimeAvoidanceWindowData where
  xi : ℝ
  xi_ge_five : 5 ≤ xi
  theta_lower : ∀ x : ℝ, xi ≤ x → 2 / 3 * x ≤ Chebyshev.theta x

def s1PrimeAvoidanceWindowActual : S1PrimeAvoidanceWindowData :=
  let h := iutIVProp21ii_theta_ge_two_thirds_eventually
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end LeanFormal.IUT.XiFPaper.Mzk1S1PrimeAvoidanceActual
end
