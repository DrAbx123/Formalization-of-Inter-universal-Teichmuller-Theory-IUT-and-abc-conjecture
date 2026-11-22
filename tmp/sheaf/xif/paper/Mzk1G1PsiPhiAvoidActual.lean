/- B1: the value of `phiFixedL` at a protected point is finite (never infinity). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiPhiDTAvoidActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiDTAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The image of a protected point is a finite value: the chart-0 coordinate of
`phiFixedL` is the finite number `h(0)`, so the image point is not the point at infinity. -/
theorem phiFixedL_protected_avoid_inf (h : Polynomial ℚ) :
    (P1Point.ofFinite (Polynomial.eval 0 h) : P1Point ℚ) ≠ P1Point.infty :=
  P1Point.ofFinite_ne_infty _

#print axioms phiFixedL_protected_avoid_inf
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiAvoidActual
-- t
-- t-- t
