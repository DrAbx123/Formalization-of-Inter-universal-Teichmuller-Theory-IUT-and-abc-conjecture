import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvBoundaryActual

/-!
# hpsi reduction (B1, G-C): thin aliases for the donor reduction lemmas

Obligation O1 of Mzk1G1B1ObligationsActual: the hPolyL form of the branch inclusion is
equivalent to the hPoly form on the p1Inv-image of the source.  The mathematical work is in
Mzk1G1PsiP1InvBoundaryActual; this file only exposes the three statements under the names used
by the B1 branch lane (no new mathematics, no new assumptions).

Donor lemmas:
* hPolyL_image_boundary_iff : hPolyL h hh '' S subset boundary <-> hPoly h hh '' (p1Inv '' S) subset boundary
* hPolyL_branch_image_boundary_iff : the same at S = Branch (psiFixed n T)
  (carries the LocallyOfFinitePresentation instance, obligation O4)
* p1Inv_image_boundarySetGlued : p1Inv '' boundary = boundary
-/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPsiReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvBoundaryActual

alias hpsi_reduction := hPolyL_image_boundary_iff
alias hpsi_branch_reduction := hPolyL_branch_image_boundary_iff
alias p1Inv_boundary_invariant := p1Inv_image_boundarySetGlued

#print axioms hpsi_reduction
#print axioms hpsi_branch_reduction
#print axioms p1Inv_boundary_invariant
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPsiReductionActual
