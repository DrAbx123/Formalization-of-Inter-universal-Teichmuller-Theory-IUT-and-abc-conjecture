/-
G1-A (route §2.2) FINAL:  pi^{-1}(A^1_lambda) = U0  and  pi^{-1}(A^1_t) = U1. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiBridge2Actual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiBridge2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
/-- The P^1 t-overlap is the basic open of the t coordinate (combining emmy's bridge
with the composite-form lemma). -/
theorem p1_overlapToChartInf_opensRange :
    Mzk1G1ProjectiveLineGluedActual.overlapToChartInf.opensRange =
      (Spec (CommRingCat.of (Polynomial ℚ))).basicOpen (secOf (Polynomial.X : Polynomial ℚ)) := by
  rw [Mzk1G1ProjectiveLineGluedActual.overlapToChartInf_opensRange_eq_composite,
    p1_overlapToChartInf_composite]
/-- Preimage of a basic open under Spec.map. -/
theorem preimage_specMap_basicOpen {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    (Spec.map f) ⁻¹ᵁ (Spec R).basicOpen (secOf r) =
      (Spec S).basicOpen (secOf (f.hom r)) := by
  rw [Scheme.preimage_basicOpen_top]
  congr 1
  have h := Scheme.ΓSpecIso_inv_naturality f
  exact (congrArg (fun g : R ⟶ Γ(Spec S, ⊤) => g.hom r) h).symm
/-- The t-chart preimage of the lambda chart is the open where r1^n is invertible. -/
theorem piChartInf_preimage_chart0 (n : Nat) :
    (piChartInf n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChart0.opensRange =
      (Spec (CommRingCat.of (ChartInfRing n))).basicOpen (secOf (r1 n ^ n)) := by
  rw [piChartInf, chartMorphismInf, Scheme.Hom.comp_preimage,
    Mzk1G1ProjectiveLineChartPreimageActual.localChartInf_preimage_localChart0,
    p1_overlapToChartInf_opensRange]
  rw [preimage_specMap_basicOpen]
  simp only [CommRingCat.hom_ofHom, evalAt_X]
/-- basicOpen of a power is inside basicOpen of the element (scheme form). -/
theorem basicOpen_pow_le (n : Nat) (hn : 0 < n) :
    (Spec (CommRingCat.of (ChartInfRing n))).basicOpen (secOf (r1 n ^ n)) ≤
      (Spec (CommRingCat.of (ChartInfRing n))).basicOpen (secOf (r1 n)) := by
  have hprime : PrimeSpectrum.basicOpen (r1 n ^ n) ≤ PrimeSpectrum.basicOpen (r1 n) := by
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
/-- The image of the overlap under the t-chart inclusion lands in the lambda chart. -/
theorem overlapImage_le_chart0 (n : Nat) :
    (fermatChartInfToCurve n) ''ᵁ (Mzk1G1FermatOverlapActual.overlapToChartInf n).opensRange ≤
      (fermatChart0ToCurve n).opensRange := by
  have hpre := Mzk1G1ProjectiveLineChartPreimageActual.preimage_opensRange_ι
    (D := Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n)
    (ULift.up true) (ULift.up false)
  have hEq : (fermatChartInfToCurve n) ''ᵁ
      (Mzk1G1FermatOverlapActual.overlapToChartInf n).opensRange =
      (fermatChartInfToCurve n).opensRange ⊓ (fermatChart0ToCurve n).opensRange := by
    rw [← hpre]
    exact Scheme.Hom.image_preimage_eq_opensRange_inf
      (f := fermatChartInfToCurve n) _
  rw [hEq]
  exact inf_le_right
/-- pi^{-1}(A^1_lambda) = U0. -/
theorem pi_preimage_localChart0 (n : Nat) (hn : 0 < n) :
    (pi n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChart0.opensRange =
      (fermatChart0ToCurve n).opensRange := by
  rw [pi_preimage_eq n]
  have hA : (fermatChart0ToCurve n) ''ᵁ ((piChart0 n) ⁻¹ᵁ
      Mzk1G1ProjectiveLineGluedActual.localChart0.opensRange) =
      (fermatChart0ToCurve n).opensRange := by
    rw [piChart0_preimage_chart0 n, Scheme.Hom.image_top_eq_opensRange]
  have hB : (fermatChartInfToCurve n) ''ᵁ ((piChartInf n) ⁻¹ᵁ
      Mzk1G1ProjectiveLineGluedActual.localChart0.opensRange) ≤
      (fermatChart0ToCurve n).opensRange := by
    rw [piChartInf_preimage_chart0 n]
    have hmono := Scheme.Hom.image_mono (f := fermatChartInfToCurve n) (basicOpen_pow_le n hn)
    have h2 : (fermatChartInfToCurve n) ''ᵁ
        (Spec (CommRingCat.of (ChartInfRing n))).basicOpen (secOf (r1 n)) ≤
        (fermatChart0ToCurve n).opensRange := by
      rw [← Mzk1G1FermatPiPreimageChartActual.overlapToChartInf_opensRange n]
      exact overlapImage_le_chart0 n
    exact hmono.trans h2
  rw [hA, sup_eq_left.mpr hB]
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual