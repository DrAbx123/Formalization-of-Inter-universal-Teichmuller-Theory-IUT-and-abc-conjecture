/-
Scratch: set-level proof of the P^1 overlap opensRange identifications (bypasses the
Opens type-ascription defeq issue). -/
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineGluedActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P1OpenScratch
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open scoped AlgebraicGeometry
theorem p1_overlapToChart0_opensRange :
    overlapToChart0.opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange]
  change Set.range overlapToChart0 =
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℚ) : Set (PrimeSpectrum (Polynomial ℚ)))
  rw [overlapToChart0]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial ℚ))
    (Polynomial.X : Polynomial ℚ)
end LeanFormal.IUT.XiFPaper.Mzk1G1P1OpenScratch
