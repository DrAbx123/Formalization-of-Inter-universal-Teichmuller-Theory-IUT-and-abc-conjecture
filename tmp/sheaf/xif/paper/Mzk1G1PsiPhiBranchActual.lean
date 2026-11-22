/- B1 branch condition: the branch locus of `phiFixedL` is contained in {0,1,inf}
(route L240-280) given the two branch conditions of the composition. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiBranchWiringActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiBranchActual
open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchWiringActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

/-- **B1 branch condition**: if the image of `psiFixed`'s branch locus under `hPolyL` and
the branch locus of `hPolyL` both lie in the Belyi boundary set, then the branch locus of
`phiFixedL = psiFixed ≫ hPolyL` lies in the boundary set. -/
theorem phi_branch_subset_boundary (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (psiFixed n T ≫ hPolyL h hh)]
    (h1 : hPolyL h hh '' Branch (psiFixed n T) ⊆ boundarySetGlued)
    (h2 : Branch (hPolyL h hh) ⊆ boundarySetGlued) :
    Branch (psiFixed n T ≫ hPolyL h hh) ⊆ boundarySetGlued :=
  branch_phiFixedL_subset_of n T h hh boundarySetGlued h1 h2

#print axioms phi_branch_subset_boundary
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiPhiBranchActual
