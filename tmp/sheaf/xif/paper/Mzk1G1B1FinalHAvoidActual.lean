import tmp.sheaf.xif.paper.Mzk1G1B1DependentActual
import tmp.sheaf.xif.paper.Mzk1G1B1Chart0Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2BranchDataActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic
/-!
# B1: **conditional assembly** with the avoidance half eliminated on the protected locus

NOTE (Lead 2026-11-17): `hbranch` (with `T ⊆ DTFixed n Tr` and `h.eval 0 ∉ {0,1}`) is an
**explicit assumption**; the analytic M2 construction giving `hbranch` is still open.
Hence `b1FiniteProducer_of_branch` is conditional; **B1 in general remains OPEN (O5)**.

`havoid` uses emmy `phiFixedL_T_avoid_data` (`Mzk1G1PsiM2BranchDataActual`), with the
`h.eval 0 ∉ {0,1}` to `aeval 0 h ∉ {0,1}` conversion `h0c_of_h0` (`B1Chart0Actual`).
The only remaining input is Henry's M2 `hbranch` (route §4.1-4.3), T-dependent form.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.B1FinalHAvoidActual
open LeanFormal.IUT.XiFPaper.B1DependentActual
open LeanFormal.IUT.XiFPaper.B1Chart0Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2BranchDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

theorem b1FiniteProducer_of_branch (n : Nat) (hn : 0 < n)
    (hbranch : ∀ T : Finset (fermatCurveScheme n),
      ∃ (Tr : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0),
        Tr.Nonempty ∧ 0 < h.natDegree ∧
        (↑T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr ∧
        h.eval 0 ∉ ({0, 1} : Set ℚ)) :
    B1FiniteProducer n :=
  b1FiniteProducer_of_dependent n hn hbranch
    (fun T Tr h hh hsub h0 =>
      phiFixedL_T_avoid_data n T Tr h hh hsub (h0c_of_h0 h0))

#print axioms b1FiniteProducer_of_branch
end LeanFormal.IUT.XiFPaper.B1FinalHAvoidActual
end