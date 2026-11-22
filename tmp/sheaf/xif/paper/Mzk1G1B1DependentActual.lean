import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic
/-!
# B1 assembly with the corrected T-dependent interface

Route §4 B1 (L235-241): input is a pair of finite disjoint geometric point sets (S,T);
the output is φ with `Branch φ ⊆ {0,1,∞}`, `φ(S) ⊆ {0,1,∞}`, `φ(T) ∩ {0,1,∞} = ∅`.
The construction (§4.1-4.3) builds ψ (and h) *depending on* (S,T): first ψ from D_T
so that ψ^{-1}(0)=D_T, then h from the finite set `ψ(S) ∪ Branch(ψ)` with `h(0) ∉ {0,1,∞}`;
hence ψ and h are **not uniformly quantified over all T**.  The earlier interface
`b1FiniteProducer_of_branch_and_avoid` with `havoid : ∀ T Tr h hh, …` was too strong;
this file gives the corrected shape: `hbranch` produces `(Tr,h)` with `T ⊆ DTFixed Tr` and
`h.eval 0 ∉ {0,1}`, and `havoid` only for those dependent data.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.B1DependentActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
variable (n : Nat)

/-- **B1 with the route-correct T-dependent interface**: `hbranch` builds the ψ/h data
from the finite set to avoid (`T ⊆ DTFixed Tr`) and the avoiding value `h(0) ∉ {0,1}`;
`havoid` is only asserted for those data. -/
theorem b1FiniteProducer_of_dependent
    (hn : 0 < n)
    (hbranch : ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
        Tr.Nonempty ∧ 0 < h.natDegree ∧
        (↑T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr ∧
        h.eval 0 ∉ ({0, 1} : Set ℚ))
    (havoid : ∀ (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ)
      (h : Polynomial ℚ) (hh : h ≠ 0),
        (↑T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr →
        h.eval 0 ∉ ({0, 1} : Set ℚ) →
        AvoidsBoundary n (phiFixedL n Tr h hh) T) :
    B1FiniteProducer n := by
  intro T
  obtain ⟨Tr, h, hh, hT, hdeg, hsub, h0⟩ := hbranch T
  refine ⟨phiFixedL n Tr h hh,
    phiFixedL_boundaryPreimage_finite n Tr h hh hn hT hdeg, ?_⟩
  exact havoid T Tr h hh hsub h0

#print axioms b1FiniteProducer_of_dependent
end LeanFormal.IUT.XiFPaper.B1DependentActual
end