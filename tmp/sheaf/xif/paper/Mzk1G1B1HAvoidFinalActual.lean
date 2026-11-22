import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0BoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import Mathlib.Tactic
/-!
# B1 havoid: the protected chart-0 points avoid the Belyi boundary

Consumes emmy's lambda-chart dictionary
`Mzk1G1PhiFixedLChart0BoundaryActual.phiFixedL_chart0_point_mem_boundary_iff`:
`phiFixedL(point) ∈ boundarySetGlued ↔ h(u) ∈ p ∨ h(u) - 1 ∈ p`.
For `p` containing `u = psiChart0Coord` (a protected point) and `h.coeff 0 ∉ {0,1}`,
`h(u) ≡ h.coeff 0 (mod p)` via `h = X * divX h + C (h.coeff 0)`; a nonzero rational is
a unit in `R n`, hence neither `h(u)` nor `h(u) - 1` vanishes at `p`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.B1HAvoidFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChart0BoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
variable (n : Nat) (T : Finset ℚ)

theorem not_mem_of_coeff_ne_zero {r : ℚ} (hr : r ≠ 0) (p : PrimeSpectrum (R n)) :
    algebraMap ℚ (R n) r ∉ p.asIdeal := by
  intro hmem
  have hunit : IsUnit (algebraMap ℚ (R n) r) := by
    refine isUnit_iff_exists_inv.mpr ⟨algebraMap ℚ (R n) r⁻¹, ?_⟩
    rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem (I := p.asIdeal) hmem hunit)

theorem aeval_not_mem_of_coeff_ne_zero (h : Polynomial ℚ) (hh0 : h.coeff 0 ≠ 0)
    (p : PrimeSpectrum (R n)) (hu : psiChart0Coord n T ∈ p.asIdeal) :
    Polynomial.aeval (psiChart0Coord n T) h ∉ p.asIdeal := by
  intro hmem
  have hsub : Polynomial.aeval (psiChart0Coord n T) h
      - psiChart0Coord n T * Polynomial.aeval (psiChart0Coord n T) (Polynomial.divX h)
      = algebraMap ℚ (R n) (h.coeff 0) := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add h]
    rw [map_add, map_mul]
    simp [Polynomial.aeval_X, Polynomial.aeval_C]
  have h1 : algebraMap ℚ (R n) (h.coeff 0) ∈ p.asIdeal := by
    rw [← hsub]
    refine Ideal.sub_mem p.asIdeal hmem ?_
    simpa [mul_comm] using Ideal.mul_mem_right
      (Polynomial.aeval (psiChart0Coord n T) (Polynomial.divX h)) p.asIdeal hu
  exact not_mem_of_coeff_ne_zero n (r := h.coeff 0) hh0 p h1

theorem aeval_sub_one_not_mem_of_coeff_ne_one (h : Polynomial ℚ) (hh1 : h.coeff 0 ≠ 1)
    (p : PrimeSpectrum (R n)) (hu : psiChart0Coord n T ∈ p.asIdeal) :
    Polynomial.aeval (psiChart0Coord n T) h - 1 ∉ p.asIdeal := by
  intro hmem
  have hsub : Polynomial.aeval (psiChart0Coord n T) h - 1
      - psiChart0Coord n T * Polynomial.aeval (psiChart0Coord n T) (Polynomial.divX h)
      = algebraMap ℚ (R n) (h.coeff 0) - 1 := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add h]
    rw [map_add, map_mul]
    simp [Polynomial.aeval_X, Polynomial.aeval_C]
    ring
  have h1 : algebraMap ℚ (R n) (h.coeff 0) - 1 ∈ p.asIdeal := by
    rw [← hsub]
    refine Ideal.sub_mem p.asIdeal hmem ?_
    simpa [mul_comm] using Ideal.mul_mem_right
      (Polynomial.aeval (psiChart0Coord n T) (Polynomial.divX h)) p.asIdeal hu
  have hcoeff : h.coeff 0 - 1 ≠ 0 := sub_ne_zero.mpr hh1
  have hmap : algebraMap ℚ (R n) (h.coeff 0) - 1 = algebraMap ℚ (R n) (h.coeff 0 - 1) :=
    by simp
  rw [hmap] at h1
  exact not_mem_of_coeff_ne_zero n hcoeff p h1

/-- **Pointwise havoid**: a protected chart-0 point avoids `{0,1,∞}` when
`h.coeff 0 ∉ {0,1}`. -/
theorem phiFixedL_chart0_notMem_boundary (h : Polynomial ℚ) (hh : h ≠ 0)
    (hh0 : h.coeff 0 ≠ 0) (hh1 : h.coeff 0 ≠ 1)
    (p : PrimeSpectrum (R n)) (hu : psiChart0Coord n T ∈ p.asIdeal) :
    phiFixedL n T h hh ((fermatChart0ToCurve n).base p) ∉ boundarySetGlued := by
  rw [phiFixedL_chart0_point_mem_boundary_iff n T h hh p]
  push_neg
  exact ⟨aeval_not_mem_of_coeff_ne_zero n T h hh0 p hu,
    aeval_sub_one_not_mem_of_coeff_ne_one n T h hh1 p hu⟩

#print axioms phiFixedL_chart0_notMem_boundary

/-- **`havoid` theorem**: for `T ⊆ DTFixed Tr`, `phiFixedL` avoids the Belyi boundary
when `h.coeff 0 ∉ {0,1}`.  This discharges the `havoid` parameter of
`Mzk1G1B1DependentActual.b1FiniteProducer_of_dependent` on the chart-0 protected locus. -/
theorem phiFixedL_avoidsBoundary_of_subset_DT (h : Polynomial ℚ) (hh : h ≠ 0)
    (hh0 : h.coeff 0 ≠ 0) (hh1 : h.coeff 0 ≠ 1)
    (T : Finset (fermatCurveScheme n)) (Tr : Finset ℚ)
    (hsub : (↑T : Set (fermatCurveScheme n)) ⊆ DTFixed n Tr) :
    AvoidsBoundary n (phiFixedL n Tr h hh) T := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hsub hx
  exact phiFixedL_chart0_notMem_boundary n Tr h hh hh0 hh1 p
    ((psiChart0Coord_mem_iff n Tr p.asIdeal).mpr hp)
#print axioms phiFixedL_avoidsBoundary_of_subset_DT
end LeanFormal.IUT.XiFPaper.B1HAvoidFinalActual
end