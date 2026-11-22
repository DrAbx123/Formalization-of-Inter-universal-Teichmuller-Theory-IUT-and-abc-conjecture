import tmp.sheaf.xif.paper.S1620ZSMulPointInductionActual
import tmp.sheaf.xif.paper.S1605PointedCurveCoeffActual
import tmp.sheaf.xif.paper.S1615AddXAddYFromDraftActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1621ZSMulPointInductionFullActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual
open LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
theorem s1621TwoZSMul :
    ∃ h : Affine.Nonsingular pointedCurve.toAffine (smulX 2) (smulY 2),
      (2 : ℤ) • s1619Point =
        Affine.Point.some (smulX 2) (smulY 2) h := by
  have hns2 : Affine.Nonsingular pointedCurve.toAffine (smulX 2) (smulY 2) := by
    have h := Affine.nonsingular_add
      (W := pointedCurve.toAffine) s1619Nonsingular s1619Nonsingular
      (fun hxy => (s1605_smulY_ne_negY 1 one_ne_zero) hxy.2)
    have hX : pointedCurve.toAffine.addX (smulX 1) (smulX 1)
        (pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)) = smulX 2 := by
      simpa [LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual.slopeOne]
        using s1615_addX_eq
    have hY : pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1)
        (pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)) = smulY 2 := by
      simpa [LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual.slopeOne]
        using s1615_addY_eq
    rwa [hX, hY] at h
  refine ⟨hns2, ?_⟩
  rw [two_zsmul]
  change s1619Point + s1619Point =
    Affine.Point.some (smulX 2) (smulY 2) hns2
  rw [show s1619Point =
    Affine.Point.some (smulX 1) (smulY 1) s1619Nonsingular from rfl,
    Affine.Point.add_self_of_Y_ne (W := pointedCurve.toAffine)
      (s1605_smulY_ne_negY 1 one_ne_zero)]
  have hX : pointedCurve.toAffine.addX (smulX 1) (smulX 1)
      (pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)) = smulX 2 := by
    simpa [LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual.slopeOne]
      using s1615_addX_eq
  have hY : pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1)
      (pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)) = smulY 2 := by
    simpa [LeanFormal.IUT.XiFPaper.S1603AffineGroupLawActual.slopeOne]
      using s1615_addY_eq
  simpa [hX, hY]
end LeanFormal.IUT.XiFPaper.S1621ZSMulPointInductionFullActual
end
