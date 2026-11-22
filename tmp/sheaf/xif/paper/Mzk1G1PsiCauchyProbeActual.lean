/- Probe (kurt): coercion NNReal norm to real norm on C (diagnostic). -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped NNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyProbeActual

theorem probe_coe_nnnorm (z : ℂ) : (‖z‖₊ : ℝ) = ‖z‖ := coe_nnnorm z

theorem probe_div_le_self {a b : ℝ≥0} (h : 1 ≤ b) : a / b ≤ a :=
  div_le_self (zero_le a) h

#print axioms probe_coe_nnnorm
#print axioms probe_div_le_self

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyProbeActual
end