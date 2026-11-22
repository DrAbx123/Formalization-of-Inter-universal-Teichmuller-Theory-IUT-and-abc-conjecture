import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual
import tmp.sheaf.xif.paper.S2482QiInvolutionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2457AffineInvolutionSquareActual

theorem S2457AffineInvolution_sq :
    S2482AffineInvolution ≫ S2482AffineInvolution = 𝟙 S2482AffineOver := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.id_left, S2482AffineInvolution, Over.homMk_left]
  change Spec.map (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) ≫
      Spec.map (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) =
    𝟙 (Spec (CommRingCat.of S2482CoordinateRing))
  rw [← Spec.map_comp, AlgebraicGeometry.Spec.map_eq_id]
  ext r
  change S2482CoordinateRingInvolution (S2482CoordinateRingInvolution r) = r
  have h := congrArg (fun f : S2482CoordinateRing →ₐ[F] S2482CoordinateRing => f r)
    S2482CoordinateRingInvolution_sq
  simpa [AlgHom.comp_apply] using h

#print axioms S2457AffineInvolution_sq

end LeanFormal.IUT.XiFPaper.S2457AffineInvolutionSquareActual

end
