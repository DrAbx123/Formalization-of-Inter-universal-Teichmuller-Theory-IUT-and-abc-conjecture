/- G-C: route §4.1 Riemann-Roch step for the general two-section map.

  `Mzk1G1PsiGeneralActual.psiGeneral` realises the scheme-level construction from arbitrary
  chart functions u0, u1 (with overlap compatibility). This file records what is already
  available for the RATIONAL case, and the precise remaining gap for a general Galois-stable
  finite set of GEOMETRIC points T:

  * DONE (this file): for T : Finset ℚ the chart functions u0 = psiChart0Coord n T,
    u1 = psiChartInfCoord n T give the compatibility `affine_compat_swapped`, hence
    psiGeneral ... = psiFixed n T (definitionally). So the rational-points case of §4.1 is
    fully within the existing two-chart machinery, and the psi^{-1}(0) = D_T / unramified-at-0
    statements for it live in the B1 lane (`psiFixed`, `psi_simple_zero`, ...).
  * GAP (general geometric T): one needs the divisor D_T = sum [t] (deg >= deg K + 3) and
    Riemann-Roch sections s0, s1 with div s0 = D_T and s1 nonzero on D_T; the ratios s0/s1
    then give u0/u1 and the compatibility. In-repo donors located by grep (see file header of
    Mzk1G1PsiGeneralActual): AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor,
    AG_FLT_RiemannRochPromotionActual (promotion_functionFieldRiemannRoch_of_riemann_and_duality),
    AG12CechRiemannRochActual (ag12_cechRiemannRoch), AG06bRRInterfaceActual (AGRiemannRochInterface).
    These are promotion-level interfaces (statements conditioned on genus/duality inputs), so
    an actual section construction still requires the underlying curve/divisor development.

  No sorry/axiom in this file. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual

variable (n : Nat) (T : Finset ℚ)

/-- route §4.1 的有理点情形：`psiGeneral` 用 `(psiChart0Coord, psiChartInfCoord)` 的兼容性
    即 `affine_compat_swapped`，得到的 morphism 就是 `psiFixed`。 -/
theorem psiGeneral_eq_psiFixed :
    psiGeneral n T (psiChart0Coord n T) (psiChartInfCoord n T)
        (affine_compat_swapped n T) =
      psiFixed n T := rfl

#print axioms psiGeneral_eq_psiFixed

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRActual
