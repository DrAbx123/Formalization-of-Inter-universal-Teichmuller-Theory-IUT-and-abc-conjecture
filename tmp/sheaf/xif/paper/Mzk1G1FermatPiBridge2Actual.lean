/-
G1-A (route §2.2): bridge lemmas for pi^{-1}(A^1_lambda) = U0.

The overlap opensRange identification for the P^1 t-chart is proved in the composite
form (no rewriting under Scheme.Hom.opensRange); the connection to overlapToChartInf is
made with congrArg on Scheme.Hom.opensRange, and used under preimage (where rewriting is
instance-safe). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageFinalActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiBridge2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
/-- The overlap of the P^1 t-chart, in composite form. -/
theorem p1_overlapToChartInf_composite :
    Scheme.Hom.opensRange
        (Spec.map (CommRingCat.ofHom Mzk1G1ProjectiveLineGluedActual.invAuto) ≫
          Mzk1G1ProjectiveLineGluedActual.overlapToChart0) =
      (Spec (CommRingCat.of (Polynomial ℚ))).basicOpen (secOf (Polynomial.X : Polynomial ℚ)) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      Mzk1G1ProjectiveLineGluedActual.invAuto)) := inferInstance
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact opensRange_localizationAway' (R := CommRingCat.of (Polynomial ℚ))
    (g := (Polynomial.X : Polynomial ℚ))
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiBridge2Actual
