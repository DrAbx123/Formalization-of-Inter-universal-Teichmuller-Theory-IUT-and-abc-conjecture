/- G-C general-T psi: `psi^{-1}(0) = D_T` formalised at the RR-data level (route §4.1).

  `Mzk1G1PsiGeneralRRDataActual.PsiGeneralRRData` packages the Riemann-Roch output
  (chart functions u0/u1 + compatibility). Here we attach the divisor D_T (as a point set of
  Y_n) together with the datum that it is exactly the coordinate-zero set of u0 on chart 0;
  `psiGeneral_preimage_p1Zero_eq` (DONE 05:24:22) then gives `psi^{-1}(0) = D_T`.

  The remaining obligations (registered, NOT claimed): (i) existence of such data for a
  general Galois-stable finite T via Riemann-Roch; (ii) unramifiedness at 0. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralRRDataActual
import tmp.sheaf.xif.paper.Mzk1G1B1GeneralPsiZeroFibreActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralZeroFibreDTActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1GeneralPsiZeroFibreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

variable (n : Nat) (T : Finset ℚ)

/-- route §4.1 的 RR 数据**加上**目标除子 `D_T` 及其与 chart-0 坐标零点集的一致性。 -/
structure PsiGeneralRRDataWithDT extends PsiGeneralRRData n T where
  /-- 目标除子（点集）：`D_T = Σ[t]`。 -/
  DT : Set (fermatCurveScheme n)
  /-- `D_T` 恰是 `u0` 在 chart-0 上的零点集。 -/
  hDT : (fermatChart0ToCurve n) ''
    {p : PrimeSpectrum (R n) | toPsiGeneralRRData.u0 ∈ p.asIdeal} = DT

/-- **一般 ψ 的 `ψ^{-1}(0) = D_T`**（由 `psiGeneral_preimage_p1Zero_eq` 直接给出）。 -/
theorem psiOfRRDataWithDT_preimage_p1Zero_eq (D : PsiGeneralRRDataWithDT n T) :
    (psiOfRRData n T D.toPsiGeneralRRData) ⁻¹' p1Zero = D.DT :=
  (psiGeneral_preimage_p1Zero_eq n T D.u0 D.u1 D.haffine).trans D.hDT

#print axioms PsiGeneralRRDataWithDT
#print axioms psiOfRRDataWithDT_preimage_p1Zero_eq

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralZeroFibreDTActual
