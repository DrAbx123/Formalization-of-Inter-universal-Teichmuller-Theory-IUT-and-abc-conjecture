/- B3: branch(phi) ⊆ hPolyL '' branch(psi) ∪ branch(hPolyL) (route L334 chain rule; donor port).
   phi = phiFixedL = psiFixed ≫ hPolyL (henry, 23:30:44). Uses the ported LANA ramification API
   (BelyiRamificationActual.branch_comp_subset, 23:24:10). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3PhiBranchActual
open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual

/-- **route L334 链式法则（B1 用）**：`branch(φ)` 落在 `hPolyL '' branch(ψ) ∪ branch(hPolyL)` 里。 -/
theorem branch_phi_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual.psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (phiFixedL n T h hh)] :
    Branch (phiFixedL n T h hh) ⊆ hPolyL h hh ''
      Branch (LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual.psiFixed n T) ∪ Branch (hPolyL h hh) := by
  have h := branch_comp_subset
    (f := LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual.psiFixed n T) (g := hPolyL h hh)
  simpa [phiFixedL] using h

#print axioms branch_phi_subset

end LeanFormal.IUT.XiFPaper.Mzk1G1B3PhiBranchActual