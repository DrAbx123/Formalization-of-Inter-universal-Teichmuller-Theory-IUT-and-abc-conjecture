/- 
# B1 (owner emmy lane): scheme-level branch support of `phiFixedL`

`phiFixedL n T h hh = psiFixed n T ≫ hPolyL h hh` (`Mzk1G1PsiHPolyLambdaActual`).
The scheme-level branch locus `Branch` is grace's ported LANA notion
(`Mzk1G1BelyiRamificationActual.Branch f = f '' Ram f`), and the composition law is
`BelyiRamification.branch_comp_subset`:

  `Branch (f ≫ g) ⊆ g '' Branch f ∪ Branch g`.

For `f = psiFixed n T`, `g = hPolyL h hh` this gives

  `Branch (phiFixedL n T h hh) ⊆ hPolyL h hh '' Branch (psiFixed n T) ∪ Branch (hPolyL h hh)`,

so it remains to place the two summands inside the Belyi boundary
`boundarySetGlued = p1Zero ∪ p1One ∪ p1Infinity` (`{0, 1, ∞} ⊆ P^1`).

## The two inclusion steps are explicit parameters (provenance)

The analytic content of each step lives in the tree, but the *scheme-level* bridge from it
is not available, so the two steps are carried as explicit hypotheses (deliberately **not**
downgraded to a `ℂ`-valued `Finset`/`Set ℂ` statement):

* `hψ : hPolyL h hh '' Branch (psiFixed n T) ⊆ boundarySetGlued`.
  Analytic content: `Branch (psiFixed n T)` is the inversion image of the critical values
  of the chart coordinate `u = psiChart0Coord n T = ∏ (X - t_i)`, i.e. of the n-th roots of
  unity (`Mzk1G1PsiBranchSetActual.branchFixedFinite` / `coe_branchFixedFinite`, and
  `Mzk1G1PsiBranchSpec.md` §2-3), and `h` sends those values into `{0,1}`
  (`Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget`, first conjunct).
* `hb : Branch (hPolyL h hh) ⊆ boundarySetGlued`.
  Analytic content: the finite critical values of `h` lie in `{0,1}`
  (`Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget`, third conjunct
  `∀ z, aeval z (derivative h) = 0 → aeval z h ∈ {0,1}`), infinity being a branch value
  automatically for a nonconstant polynomial.  No scheme-level `Branch (hPolyL h hh)`
  donor exists in the tree (hPolyL is glued from `p1Inv ≫ hPoly ≫ p1Inv`), hence the
  explicit parameter.

## Note on the `LocallyOfFinitePresentation` arguments

`Branch` is only defined for locally-of-finite-presentation morphisms; those instances are
carried as typeclass hypotheses (they are not yet constructed for `psiFixed`/`hPolyL` in the
tree, cf. `Mzk1G1B3PhiBranchActual` and `Mzk1G1PsiBranchWiringActual`).  For the composite
statement the instance is synthesized by `locallyOfFinitePresentation_comp`; the
`phiFixedL`-named form additionally carries the instance for `phiFixedL` itself because
`phiFixedL` is a plain definition and typeclass search does not unfold it.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1BelyiRamificationActual
import tmp.sheaf.xif.paper.Mzk1G1PsiBranchSetActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1PsiBranchWiringActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBranchSupportActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchSetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open scoped AlgebraicGeometry

/-- **Chain rule, composite form**: the branch locus of
`psiFixed n T ≫ hPolyL h hh` lies in the image of `Branch (psiFixed n T)` under
`hPolyL h hh`, together with `Branch (hPolyL h hh)`
(grace's `BelyiRamification.branch_comp_subset`). -/
theorem branch_phiFixedL_comp_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)] :
    Branch (psiFixed n T ≫ hPolyL h hh) ⊆
      hPolyL h hh '' Branch (psiFixed n T) ∪ Branch (hPolyL h hh) :=
  BelyiRamification.branch_comp_subset (psiFixed n T) (hPolyL h hh)

/-- **Branch support of `phiFixedL`, composite form**: if the image under `hPolyL h hh` of
`Branch (psiFixed n T)` and the branch locus `Branch (hPolyL h hh)` both lie in the Belyi
boundary `{0, 1, ∞}`, then so does `Branch (psiFixed n T ≫ hPolyL h hh)`. -/
theorem branch_phiFixedL_comp_subset_boundary (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    (hψ : hPolyL h hh '' Branch (psiFixed n T) ⊆ boundarySetGlued)
    (hb : Branch (hPolyL h hh) ⊆ boundarySetGlued) :
    Branch (psiFixed n T ≫ hPolyL h hh) ⊆ boundarySetGlued :=
  (branch_phiFixedL_comp_subset n T h hh).trans (Set.union_subset hψ hb)

/-- **Scheme-level branch support of `phiFixedL` (B1 branch condition)**:
`Branch (phiFixedL n T h hh) ⊆ {0, 1, ∞}` in `P^1` (`boundarySetGlued`).

The two analytic inputs are explicit parameters `hψ` and `hb` (provenance in the file
header; both are consumed from `Mzk1G1PsiBranchSetActual` + `Mzk1G1PsiM2AnalyticActual`
once a scheme-level P^1-value dictionary is available).  No `ℂ`-valued downgrade is used:
the statement is the scheme-theoretic branch locus of grace's `BelyiRamification.Branch`. -/
theorem phiFixedL_branch_subset (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (psiFixed n T)]
    [LocallyOfFinitePresentation (hPolyL h hh)]
    [LocallyOfFinitePresentation (phiFixedL n T h hh)]
    (hψ : hPolyL h hh '' Branch (psiFixed n T) ⊆ boundarySetGlued)
    (hb : Branch (hPolyL h hh) ⊆ boundarySetGlued) :
    Branch (phiFixedL n T h hh) ⊆ boundarySetGlued :=
  branch_phiFixedL_comp_subset_boundary n T h hh hψ hb

/-! ## Axiom checks -/

#print axioms branch_phiFixedL_comp_subset
#print axioms branch_phiFixedL_comp_subset_boundary
#print axioms phiFixedL_branch_subset

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBranchSupportActual
