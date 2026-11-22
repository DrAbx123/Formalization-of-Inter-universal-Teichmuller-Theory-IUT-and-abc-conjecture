/- B1 branch wiring: the branch locus of `phiFixedL` is controlled by the branch loci of
`psiFixed` and `hPolyL` (grace's `Mzk1G1BelyiRamificationActual.Branch`/`branch_comp_subset`). -/
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchWiringActual
open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-- The branch locus of `phiFixedL = psiFixed ≫ hPolyL` is contained in the image of the
branch locus of `psiFixed` under `hPolyL`, together with the branch locus of `hPolyL`
(composition law for branch loci, grace's `branch_comp_subset`). -/
theorem branch_phiFixedL_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (psiFixed n T ≫ hPolyL h hh)] :
    Branch (psiFixed n T ≫ hPolyL h hh) ⊆
      hPolyL h hh '' Branch (psiFixed n T) ∪ Branch (hPolyL h hh) :=
  branch_comp_subset (psiFixed n T) (hPolyL h hh)

/-- B1 branch condition: if the image of `psiFixed`'s branch locus under `hPolyL` and the
branch locus of `hPolyL` are both contained in the boundary set, then so is the branch
locus of `phiFixedL`. -/
theorem branch_phiFixedL_subset_of (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (psiFixed n T ≫ hPolyL h hh)]
    (S : Set projectiveLineGlued)
    (h1 : hPolyL h hh '' Branch (psiFixed n T) ⊆ S)
    (h2 : Branch (hPolyL h hh) ⊆ S) :
    Branch (psiFixed n T ≫ hPolyL h hh) ⊆ S :=
  (branch_phiFixedL_subset n T h hh).trans (Set.union_subset h1 h2)

#print axioms branch_phiFixedL_subset
#print axioms branch_phiFixedL_subset_of
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchWiringActual
