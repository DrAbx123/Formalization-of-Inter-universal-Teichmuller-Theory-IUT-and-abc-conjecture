/- G-C general-T psi via Riemann-Roch: the RR input data and its scheme-level construction.

  Route §4.1: for a Galois-stable finite set of geometric points T with deg D_T >= deg K + 3,
  Riemann-Roch produces global sections s0, s1 of O(D_T) with div s0 = D_T and s1 nonzero on
  D_T; their ratios give the chart functions u0 (chart 0) and u1 (infinity chart) and the
  overlap compatibility. `Mzk1G1PsiGeneralActual.psiGeneral` then glues the morphism.

  This file packages that input as `PsiGeneralRRData` (an intermediate data structure, NOT a
  claimed proof: the existence of the data for general T is registered as an explicit obligation)
  and proves the scheme-level consequences that do not depend on how the data are produced:
  * the zero-fibre dictionary on chart 0: `psi (chart0 p) ∈ p1Zero ↔ u0 ∈ p`, and
  * the inclusion `u0`-zeros ⊆ psi^{-1}(p1Zero).

  In-repo RR donors (located by grep): tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor
  (`AlgebraicCurve.lSpaceOn`, `cechH0`), AG_FLT_RiemannRochPromotionActual,
  AG12CechRiemannRochActual, AG06bRRInterfaceActual. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B1GeneralPsiZeroFibreActual
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1GeneralPsiZeroFibreActual

variable (n : Nat) (T : Finset ℚ)

/-- **route §4.1 的 RR 输入数据**：chart 函数 `u0`/`u1` 与 overlap 兼容。
    该数据的**存在性**对一般 T 由 Riemann-Roch 给出（登记为显式义务，见文件头）。 -/
structure PsiGeneralRRData where
  /-- chart-0 的 chart 函数（= s0/s1 在 chart-0 上的限制）。 -/
  u0 : R n
  /-- chart-∞ 的 chart 函数。 -/
  u1 : Localization.Away (psiChartInfDenom n T)
  /-- overlap 兼容（route §4.1 的 s0/s1 一致性）。 -/
  haffine : chart0ToOverlap n T ≫ chartMorphism0 u0 =
    chartInfPieceToOverlap n T ≫ chartMorphismInf u1

/-- 由 RR 数据得到的实际 morphism `Y_n ⟶ P¹`（= `psiGeneral`）。 -/
noncomputable def psiOfRRData (D : PsiGeneralRRData n T) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  psiGeneral n T D.u0 D.u1 D.haffine

/-- **chart-0 零纤维字典**（对 RR 数据）。 -/
theorem psiOfRRData_chart0_mem_p1Zero_iff (D : PsiGeneralRRData n T)
    (p : PrimeSpectrum (R n)) :
    psiOfRRData n T D ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔ D.u0 ∈ p.asIdeal :=
  psiGeneral_chart0_mem_p1Zero_iff n T D.u0 D.u1 D.haffine p

/-- **chart-0 零纤维包含**：`u0` 的零点集打到 `p1Zero`。 -/
theorem psiOfRRData_chart0_image_subset (D : PsiGeneralRRData n T) :
    (fermatChart0ToCurve n) '' {p : PrimeSpectrum (R n) | D.u0 ∈ p.asIdeal} ⊆
      psiOfRRData n T D ⁻¹' p1Zero :=
  psiGeneral_chart0_image_subset_p1Zero n T D.u0 D.u1 D.haffine

#print axioms PsiGeneralRRData
#print axioms psiOfRRData
#print axioms psiOfRRData_chart0_mem_p1Zero_iff
#print axioms psiOfRRData_chart0_image_subset

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRDataActual
