/-
G1-A (route §2.2) FINAL:  pi^{-1}(A^1_t) = U1  (symmetric of pi_preimage_localChart0). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageCloseActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageClose2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
/-- The P^1 lambda-chart overlap is the basic open of the coordinate. -/
theorem p1_overlapToChart0_opensRange :
    Mzk1G1ProjectiveLineGluedActual.overlapToChart0.opensRange =
      (Spec (CommRingCat.of (Polynomial ℚ))).basicOpen (secOf (Polynomial.X : Polynomial ℚ)) :=
  opensRange_localizationAway' (R := CommRingCat.of (Polynomial ℚ))
    (g := (Polynomial.X : Polynomial ℚ))
/-- The lambda-chart preimage of the t chart is the open where x0^n is invertible. -/
theorem piChart0_preimage_chartInf (n : Nat) :
    (piChart0 n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChartInf.opensRange =
      (Spec (CommRingCat.of (Chart0Ring n))).basicOpen (secOf (x0 n ^ n)) := by
  rw [piChart0, chartMorphism0, Scheme.Hom.comp_preimage,
    Mzk1G1ProjectiveLineChartPreimageActual.localChart0_preimage_localChartInf,
    p1_overlapToChart0_opensRange, preimage_specMap_basicOpen]
  simp only [CommRingCat.hom_ofHom, evalAt_X]
/-- basicOpen of a power of x0 is inside basicOpen of x0. -/
theorem basicOpen_pow_le_chart0 (n : Nat) (hn : 0 < n) :
    (Spec (CommRingCat.of (Chart0Ring n))).basicOpen (secOf (x0 n ^ n)) ≤
      (Spec (CommRingCat.of (Chart0Ring n))).basicOpen (secOf (x0 n)) := by
  have hprime : PrimeSpectrum.basicOpen (x0 n ^ n) ≤ PrimeSpectrum.basicOpen (x0 n) := by
    intro p hp
    rw [PrimeSpectrum.mem_basicOpen] at hp ⊢
    intro hf
    refine hp ?_
    induction n with
    | zero => exact absurd hn (Nat.lt_irrefl 0)
    | succ k ih =>
      rw [pow_succ]
      exact p.asIdeal.mul_mem_left _ hf
  simp only [secOf]
  rw [basicOpen_eq_of_affine, basicOpen_eq_of_affine]
  exact hprime
/-- The image of the lambda-chart overlap lands in the t chart. -/
theorem overlapImage_le_chartInf (n : Nat) :
    (fermatChart0ToCurve n) ''ᵁ (Mzk1G1FermatOverlapActual.overlapToChart0 n).opensRange ≤
      (fermatChartInfToCurve n).opensRange := by
  have hpre := Mzk1G1ProjectiveLineChartPreimageActual.preimage_opensRange_ι
    (D := Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n)
    (ULift.up false) (ULift.up true)
  have hEq : (fermatChart0ToCurve n) ''ᵁ
      (Mzk1G1FermatOverlapActual.overlapToChart0 n).opensRange =
      (fermatChart0ToCurve n).opensRange ⊓ (fermatChartInfToCurve n).opensRange := by
    rw [← hpre]
    exact Scheme.Hom.image_preimage_eq_opensRange_inf
      (f := fermatChart0ToCurve n) _
  rw [hEq]
  exact inf_le_right
/-- pi^{-1}(A^1_t) = U1. -/
theorem pi_preimage_localChartInf (n : Nat) (hn : 0 < n) :
    (pi n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChartInf.opensRange =
      (fermatChartInfToCurve n).opensRange := by
  rw [pi_preimage_eq n]
  have hA : (fermatChartInfToCurve n) ''ᵁ ((piChartInf n) ⁻¹ᵁ
      Mzk1G1ProjectiveLineGluedActual.localChartInf.opensRange) =
      (fermatChartInfToCurve n).opensRange := by
    rw [piChartInf_preimage_chartInf n, Scheme.Hom.image_top_eq_opensRange]
  have hB : (fermatChart0ToCurve n) ''ᵁ ((piChart0 n) ⁻¹ᵁ
      Mzk1G1ProjectiveLineGluedActual.localChartInf.opensRange) ≤
      (fermatChartInfToCurve n).opensRange := by
    rw [piChart0_preimage_chartInf n]
    have hmono := Scheme.Hom.image_mono (f := fermatChart0ToCurve n) (basicOpen_pow_le_chart0 n hn)
    have h2 : (fermatChart0ToCurve n) ''ᵁ
        (Spec (CommRingCat.of (Chart0Ring n))).basicOpen (secOf (x0 n)) ≤
        (fermatChartInfToCurve n).opensRange := by
      rw [← Mzk1G1FermatPiPreimageChartActual.overlapToChart0_opensRange n]
      exact overlapImage_le_chartInf n
    exact hmono.trans h2
  rw [hA, sup_eq_right.mpr hB]
#print axioms pi_preimage_localChart0
#print axioms pi_preimage_localChartInf
/- final: both pi preimage equalities; axioms clean. -/
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageClose2Actual