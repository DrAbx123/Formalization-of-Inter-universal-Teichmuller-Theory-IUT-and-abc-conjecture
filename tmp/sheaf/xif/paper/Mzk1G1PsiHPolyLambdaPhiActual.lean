/-
# B1 phi layer in the lambda coordinate: unpacked forms and chart pieces of `phiFixedL`

Donor (read-only): `Mzk1G1PsiHPolyLambdaActual` (henry, DONE 23:30:44):

  hPolyL h hh = p1Inv ≫ hPoly h hh ≫ p1Inv               (hPolyL_def)
  localChart0 ≫ hPolyL h hh = chartMorphism0 h          (hPolyL_lambda_chart)
  phiFixedL n T h hh = psiFixed n T ≫ hPolyL h hh

`phiFixedL` is the B1 morphism in the lambda coordinate: since `psiFixed` sends the first
Fermat chart to the **lambda** chart (`lambda = u`) and `hPolyL` acts by `lambda ↦ h(lambda)`,
the composite `phiFixedL` acts on the first chart by `lambda' = h(u)` — the chart-swap
counterpart of `phiFixed = psiFixed ≫ hPoly`, whose first chart imposes `t = h(1/u)`.

This file only records the definitional unpackings of `phiFixedL` (`rfl`-level) and its two
chart restrictions, because `Mzk1G1PsiHPolyLambdaActual` stops at the definition.
Consumers: the phiFixedL fibre-finiteness layer (B1).

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaPhiActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

/-! ## 1. Definitional unpackings -/

/-- Definitional unfolding of `phiFixedL`: `psiFixed` followed by `hPolyL`. -/
theorem phiFixedL_def (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    phiFixedL n T h hh = psiFixed n T ≫ hPolyL h hh := rfl

/-- The fully unpacked composite: `psiFixed` followed by the two inversions around `hPoly`. -/
theorem phiFixedL_unfold (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    phiFixedL n T h hh = psiFixed n T ≫ (p1Inv ≫ hPoly h hh ≫ p1Inv) := by
  rw [phiFixedL_def, hPolyL_def]

/-- The unpacked composite in the association used by chart computations (the two middle
factors `p1Inv ≫ hPoly` are the t-chart description of `hPoly`). -/
theorem phiFixedL_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    phiFixedL n T h hh = psiFixed n T ≫ p1Inv ≫ hPoly h hh ≫ p1Inv :=
  phiFixedL_unfold n T h hh

/-- `phiFixedL` restricted to the first piece of the cover: the lambda chart map
`lambda = u = psiChart0Coord` followed by `hPolyL`. -/
theorem phiFixedL_ι_false (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ phiFixedL n T h hh =
      chartMorphism0 (R := R n) (psiChart0Coord n T) ≫ hPolyL h hh := by
  rw [phiFixedL, ← Category.assoc, psiFixed_ι_false]
  rfl

/-- `phiFixedL` restricted to the second piece of the cover (`qPiece`, coordinate
`v = psiChartInfCoord`, which `psiFixed` sends to the t-chart with `t = v`). -/
theorem phiFixedL_ι_true (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫ phiFixedL n T h hh =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T) ≫
        hPolyL h hh := by
  rw [phiFixedL, ← Category.assoc, psiFixed_ι_true]
  rfl

/-! ## Axiom checks -/

#print axioms phiFixedL_def
#print axioms phiFixedL_unfold
#print axioms phiFixedL_eq
#print axioms phiFixedL_ι_false
#print axioms phiFixedL_ι_true

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaPhiActual
