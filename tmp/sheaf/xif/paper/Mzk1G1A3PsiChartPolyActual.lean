/- A3 / F2.2: identification of the psi chart-0 coordinate as a univariate polynomial in `x`.

  `psiChart0Coord n T = prod (x - t)` is the evaluation at the chart-0 coordinate `x` of the
  univariate protected polynomial `protectedToZeroPolynomial T = prod (X - C t)`
  (`Mzk1G1ProtectedToZeroMapActual`). This is the first ingredient of the F2.2 dictionary:
  the value layer (`psi_unramified_over_zero`, `psi_simple_zero`) is about this univariate
  polynomial, and the scheme-level chart map is `chartMorphism0 (psiChart0Coord n T)`.
  Remaining F2.2 obligations (registered in coord/EXPLICIT-PARAM-AUDIT-GRACE.md §F2.2):
  (a) the Kaehler chain rule `D (aeval x g) = aeval x g' . D x` for the chart coordinate;
  (b) the multivariate chart smoothness criterion (Omega rank 1 + nonvanishing of `du`), with
      the arithmetic caveat: at points with `y = 0` (i.e. `t^n = 1`) the chart coordinate `x`
      itself is ramified (`dx = 0`), so F2.2 must carry a hypothesis `hT : forall t in T, t^n != 1`.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3PsiChartPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

variable (n : Nat)

/-- **chart-0 坐标就是一元 protected 多项式在 `x` 处的取值**。 -/
theorem psiChart0Coord_eq_aeval_protectedToZero (T : Finset ℚ) :
    psiChart0Coord n T =
      Polynomial.aeval (chartX n) (protectedToZeroPolynomial (K := ℚ) T) := by
  unfold psiChart0Coord protectedToZeroPolynomial
  rw [map_prod]
  refine Finset.prod_congr rfl ?_
  intro t _
  simp

#print axioms psiChart0Coord_eq_aeval_protectedToZero

end LeanFormal.IUT.XiFPaper.Mzk1G1A3PsiChartPolyActual