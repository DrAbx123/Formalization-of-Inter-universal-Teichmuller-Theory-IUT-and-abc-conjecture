/-
G1-A (route §2.2): the preimages of the two affine charts of P^1 under pi.
  pi^{-1}(A^1_lambda) = U0,   pi^{-1}(A^1_t) = U1. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageChartActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
/-- The lambda chart preimage of the lambda chart is everything. -/
theorem piChart0_preimage_chart0 (n : Nat) :
    (piChart0 n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChart0.opensRange = ⊤ := by
  rw [piChart0, Mzk1G1ProjectiveLineTransitionActual.chartMorphism0,
    Scheme.Hom.comp_preimage,
    ← Mzk1G1ProjectiveLineGluedActual.localChart0.image_top_eq_opensRange,
    Mzk1G1ProjectiveLineGluedActual.localChart0.preimage_image_eq]
  simp
/-- The t chart preimage of the t chart is everything. -/
theorem piChartInf_preimage_chartInf (n : Nat) :
    (piChartInf n) ⁻¹ᵁ Mzk1G1ProjectiveLineGluedActual.localChartInf.opensRange = ⊤ := by
  rw [piChartInf, Mzk1G1ProjectiveLineTransitionActual.chartMorphismInf,
    Scheme.Hom.comp_preimage,
    ← Mzk1G1ProjectiveLineGluedActual.localChartInf.image_top_eq_opensRange,
    Mzk1G1ProjectiveLineGluedActual.localChartInf.preimage_image_eq]
  simp
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageFinalActual