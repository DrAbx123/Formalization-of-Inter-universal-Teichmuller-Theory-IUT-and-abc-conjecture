/- B1 analytic h (kurt): consumer-facing Cauchy bound wrappers for PsiPhiD / M2.

Re-exports the merged entry bounds in the shapes used by the analytic h producer.
Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyEntryActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyEntryActual

/-- Unit-disc value bound (consumer form). -/
theorem eval_bound_unit_disc (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (α : ℂ) (hα : ‖α‖ ≤ 1) :
    ‖p.eval α‖ ≤ 2 ^ p.natDegree :=
  eval_bound_entry p hp hroots α hα

/-- Root bound from a coefficient bound (consumer form). -/
theorem root_bound_of_coeff_bound (p : ℂ[X]) (hp : p ≠ 0) (hmonic : p.Monic)
    (B : ℝ≥0) (hcoeff : ∀ i, ‖p.coeff i‖₊ ≤ B) {z : ℂ} (hz : p.IsRoot z) :
    ‖z‖ ≤ 1 + (B : ℝ) :=
  root_bound_entry p hp hmonic B hcoeff hz

/-- The explicit B(d0) in the M2 recursion is at least one. -/
theorem one_le_psiB (d : ℕ) : 1 ≤ Mzk1G1PsiB3AlgPointActual.psiB d := by
  unfold Mzk1G1PsiB3AlgPointActual.psiB
  have h : (0 : ℝ) ≤ (d : ℝ) * 2 ^ d := by positivity
  linarith

/-- The explicit B(d0) is monotone in the degree. -/
theorem psiB_mono : Monotone Mzk1G1PsiB3AlgPointActual.psiB := by
  intro a b hab
  unfold Mzk1G1PsiB3AlgPointActual.psiB
  have h1 : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ b := by
    exact pow_le_pow_right₀ (by norm_num) hab
  have hnonneg : (0 : ℝ) ≤ (a : ℝ) := by positivity
  nlinarith

/-- Algebraic-point critical bound (consumer form of batch 3b). -/
theorem algPoint_critical_bound (p : Mzk1G1PsiM2ProducerActual.AlgPoint)
    (hroots : ∀ z ∈ (Mzk1G1PsiB3AlgPointActual.algPointPoly p).roots, ‖z‖ ≤ 1)
    {z : ℂ} (hz : (Mzk1G1PsiB3AlgPointActual.algPointPoly p).derivative.IsRoot z)
    (hd : 1 ≤ p.deg) :
    ‖z‖ ≤ Mzk1G1PsiB3AlgPointActual.psiB p.deg :=
  algPoint_derivative_bound_entry p hroots hz hd

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyConsumerActual
end