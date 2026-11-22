/- B1/O3 value layer: critical values of the M2 analytic polynomial lie in {0,1}.

  Input: `Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget` third conjunct (derivative-zero
  implies value in {0,1}). Output: the corresponding `Polynomial.criticalValues` statement,
  which is the value-level half of the O3 dictionary (scheme-level `Branch hPoly` is the
  remaining gap, registered separately). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1O3ValueLayerActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual

/-- **O3 值层**：M2 解析目标给出的多项式，其导数零点处的值落在 `{0,1}`。 -/
theorem o3a_aeval_of_derivative_zero {Branch : Finset ℂ}
    (tgt : M2AnalyticTarget Branch) (z : ℂ)
    (hz : Polynomial.aeval z (Polynomial.derivative tgt.choose) = 0) :
    Polynomial.aeval z tgt.choose ∈ ({0, 1} : Set ℂ) := by
  exact tgt.choose_spec.2.2.1 z hz

/-- **O3 值层（criticalValues 形式）**：`criticalValues q ⊆ {0,1}`。 -/
theorem o3a_criticalValues_subset {Branch : Finset ℂ}
    (tgt : M2AnalyticTarget Branch) :
    (Polynomial.criticalValues (S := ℂ) tgt.choose) ⊆ ({0, 1} : Set ℂ) := by
  rintro c ⟨z, hz, rfl⟩
  exact o3a_aeval_of_derivative_zero tgt z
    (Polynomial.aeval_eq_zero_of_mem_rootSet hz)

#print axioms o3a_aeval_of_derivative_zero
#print axioms o3a_criticalValues_subset

end LeanFormal.IUT.XiFPaper.Mzk1G1B1O3ValueLayerActual