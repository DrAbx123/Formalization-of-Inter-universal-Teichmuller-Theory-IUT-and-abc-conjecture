/- hPoly ③, cover part: open-immersion instances for the three cover pieces. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyActual
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
variable (h : Polynomial ℚ)
/-- Piece 0 (the t-chart) is an open immersion. -/
instance isOpenImmersion_hPolyPiece0 : IsOpenImmersion hPolyPiece0 := by
  unfold hPolyPiece0
  infer_instance
/-- Piece 1 (D(lambda) inside the lambda chart) is an open immersion. -/
instance isOpenImmersion_hPolyPiece1 : IsOpenImmersion hPolyPiece1 := by
  unfold hPolyPiece1
  infer_instance
/-- Piece 2 (D(hRev) inside the lambda chart) is an open immersion. -/
instance isOpenImmersion_hPolyPiece2 (h : Polynomial ℚ) : IsOpenImmersion (hPolyPiece2 h) := by
  unfold hPolyPiece2
  infer_instance
#print axioms isOpenImmersion_hPolyPiece0
#print axioms isOpenImmersion_hPolyPiece1
#print axioms isOpenImmersion_hPolyPiece2
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyCoverActual