/- B1 analytic h (kurt): merged entry point for the Cauchy-type bounds.

Re-exports batch1/2/3/3b so consumers (PsiPhiD / M2 recursion) import a single module.
No new declarations except the trivial re-export wrappers.

Default heartbeats (no maxHeartbeats option in this file).
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyBoundActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCauchyBound3Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiB3AlgPointActual

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyEntryActual

/-- Batch-1 evaluation bound re-export. -/
theorem eval_bound_entry (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (α : ℂ) (hα : ‖α‖ ≤ 1) :
    ‖p.eval α‖ ≤ 2 ^ p.natDegree :=
  Mzk1G1PsiCauchyBoundActual.norm_eval_prod_bound p hp hroots α hα

/-- Batch-2 Cauchy root bound re-export. -/
theorem root_bound_entry (p : ℂ[X]) (hp : p ≠ 0) (hmonic : p.Monic) (B : ℝ≥0)
    (hcoeff : ∀ i, ‖p.coeff i‖₊ ≤ B) {z : ℂ} (hz : p.IsRoot z) :
    ‖z‖ ≤ 1 + (B : ℝ) :=
  Mzk1G1PsiCauchyBoundActual.cauchy_root_bound p hp hmonic B hcoeff hz

/-- Batch-3 coefficient bound re-export. -/
theorem coeff_bound_entry (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ 1) (k : ℕ) :
    ‖p.coeff k‖ ≤ (Nat.choose p.natDegree k : ℝ) :=
  Mzk1G1PsiCauchyBound3Actual.coeff_norm_le_choose p hp hroots k

/-- Batch-3b B(d0) bound for algebraic points (unit-disc conjugates). -/
theorem algPoint_derivative_bound_entry (p : Mzk1G1PsiM2ProducerActual.AlgPoint)
    (hroots : ∀ z ∈ (Mzk1G1PsiB3AlgPointActual.algPointPoly p).roots, ‖z‖ ≤ 1)
    {z : ℂ} (hz : (Mzk1G1PsiB3AlgPointActual.algPointPoly p).derivative.IsRoot z)
    (hd : 1 ≤ p.deg) :
    ‖z‖ ≤ Mzk1G1PsiB3AlgPointActual.psiB p.deg :=
  Mzk1G1PsiB3AlgPointActual.algPoint_derivative_root_bound p hroots hz hd

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyEntryActual
end