/- B1: rational chart-0 points really land in `psi^{-1}(0)` (via the RR instance).

  Combining `Mzk1G1B1DTSubsetActual` (a point with rational chart-0 coordinate t lies in
  `DTFixed n (S.image f)`), the RR instance `psiGeneralRRDataOfFinset`, and
  `psiGeneralRRDataOfFinset_preimage_p1Zero_eq` (`psi^{-1}(0) = DTFixed`), every such point
  is in the zero fibre of the psi morphism. This is the B1 `T ⊆ DTFixed ⟹ T ⊆ psi^{-1}(0)`
  consumption link at the RR-data interface. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralRRInstanceActual
import tmp.sheaf.xif.paper.Mzk1G1B1DTSubsetActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1DTZeroFibreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralRRInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1DTSubsetActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

variable (n : Nat)

/-- **B1 消费链**：chart-0 有理坐标点落在 `psi^{-1}(p1Zero)` 中（RR 实例 + DTFixed 选取）。 -/
theorem chart0_point_mem_psiGeneral_preimage_p1Zero
    (S : Finset (PrimeSpectrum (R n))) (f : PrimeSpectrum (R n) → ℚ)
    (hf : ∀ q ∈ S, chartX n - algebraMap ℚ (R n) (f q) ∈ q.asIdeal)
    (p : PrimeSpectrum (R n)) (hp : p ∈ S) :
    (fermatChart0ToCurve n).base p ∈
      (psiOfRRData n (S.image f)
        (psiGeneralRRDataOfFinset n (S.image f)).toPsiGeneralRRData) ⁻¹' p1Zero :=
  (psiGeneralRRDataOfFinset_preimage_p1Zero_eq n (S.image f)).symm ▸
    chart0_point_mem_DTFixed_of_rational n S f hf p hp

#print axioms chart0_point_mem_psiGeneral_preimage_p1Zero
/-- **B2 全局定理的独立复算**（经 RR 实例链）：`psiFixed^{-1}(p1Zero) = DTFixed`。 -/
theorem psiFixed_preimage_p1Zero_eq_DTFixed_viaRR (T : Finset ℚ) :
    psiFixed n T ⁻¹' p1Zero = DTFixed n T := by
  rw [← psiGeneralRRDataOfFinset_eq_psiFixed n T]
  exact psiGeneralRRDataOfFinset_preimage_p1Zero_eq n T

#print axioms psiFixed_preimage_p1Zero_eq_DTFixed_viaRR


end LeanFormal.IUT.XiFPaper.Mzk1G1B1DTZeroFibreActual