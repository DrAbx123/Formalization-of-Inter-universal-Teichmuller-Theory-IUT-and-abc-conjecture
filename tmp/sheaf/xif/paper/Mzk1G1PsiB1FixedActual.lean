import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import Mathlib.Tactic
/-!
# B1 fixed: `phiFixed = psiFixed ≫ hPoly` and its chart restrictions

`Mzk1G1PsiB1Actual` defines `phi = psi ≫ hPoly` using henry's uncorrected `psi` and the
finite-beta polynomial `h`.  Here we use the corrected `psiFixed` (chart swap, B2 direction)
and expose its two chart restrictions, which are what the finite-fibre and avoidance
arguments consume.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
variable (n : Nat) (T : Finset ℚ)

/-- The corrected composite `phiFixed = psiFixed ≫ hPoly`, used for B1. -/
noncomputable def phiFixed (h : Polynomial ℚ) (hh : h ≠ 0) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  psiFixed n T ≫ hPoly h hh

theorem phiFixed_ι_false (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ phiFixed n T h hh =
      chartMorphism0 (R := R n) (psiChart0Coord n T) ≫ hPoly h hh := by
  rw [phiFixed, ← Category.assoc, psiFixed_ι_false]
  rfl

theorem phiFixed_ι_true (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫ phiFixed n T h hh =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T)
        ≫ hPoly h hh := by
  rw [phiFixed, ← Category.assoc, psiFixed_ι_true]
  rfl

#print axioms phiFixed
#print axioms phiFixed_ι_false
#print axioms phiFixed_ι_true
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1FixedActual
end