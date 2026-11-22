/-
G1-A (route §2.2): preimages of the two affine charts of P^1 under pi, part 1
(overlap opensRange identifications).  Uses grace's coercion interface
Mzk1SchemeOpensRangeInterfaceActual.opensRange_localizationAway'. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import tmp.sheaf.xif.paper.Mzk1SchemeOpensRangeInterfaceActual
import Mathlib.AlgebraicGeometry.AffineScheme
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
/-- The section of the structure sheaf of Spec R corresponding to r : R. -/
def secOf {R : CommRingCat} (r : R) : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv r
/-- The P^1 overlap of the lambda chart is the basic open of the coordinate. -/
theorem p1_Mzk1G1ProjectiveLineGluedActual.overlapToChart0_opensRange :
    Mzk1G1ProjectiveLineGluedActual.overlapToChart0.opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange]
  change Set.range Mzk1G1ProjectiveLineGluedActual.overlapToChart0 =
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) : Set (PrimeSpectrum (Polynomial ℚ)))
  rw [Mzk1G1ProjectiveLineGluedActual.overlapToChart0]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial ℚ))
    (Polynomial.X : Polynomial ℚ)
/-- The Y-side overlap of the first chart is the basic open of x0. -/
theorem overlapToChart0_opensRange (n : Nat) :
    (Mzk1G1FermatOverlapActual.overlapToChart0 n).opensRange =
      (Spec (CommRingCat.of (Chart0Ring n))).basicOpen
        (secOf (Mzk1G1FermatOverlapActual.x0 n)) := by
  show (Spec.map (CommRingCat.ofHom
      (algebraMap (Chart0Ring n) (Mzk1G1FermatOverlapActual.Overlap0 n)))).opensRange = _
  exact opensRange_localizationAway' (R := CommRingCat.of (Chart0Ring n))
    (g := Mzk1G1FermatOverlapActual.x0 n)
/-- The Y-side overlap of the second chart is the basic open of r1. -/
theorem overlapToChartInf_opensRange (n : Nat) :
    (Mzk1G1FermatOverlapActual.overlapToChartInf n).opensRange =
      (Spec (CommRingCat.of (ChartInfRing n))).basicOpen
        (secOf (Mzk1G1FermatOverlapActual.r1 n)) := by
  haveI : IsIso (Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom := inferInstance
  show ((Mzk1G1FermatOverlapActual.overlapSchemeIso n).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (ChartInfRing n) (Mzk1G1FermatOverlapActual.OverlapInf n)))).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact opensRange_localizationAway' (R := CommRingCat.of (ChartInfRing n))
    (g := Mzk1G1FermatOverlapActual.r1 n)
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual