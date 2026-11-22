import tmp.sheaf.xif.paper.S1619UniversalPointLayerActual
import tmp.sheaf.xif.paper.S1617SmulAddFromDraftActual
import tmp.sheaf.xif.paper.S1615AddXAddYFromDraftActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1620ZSMulPointInductionActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1619UniversalPointLayerActual
open LeanFormal.IUT.XiFPaper.S1617SmulAddFromDraftActual
open LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
theorem s1620OneZSMul :
    (1 : ℤ) • s1619Point =
      Affine.Point.some (smulX 1) (smulY 1) s1619Nonsingular := by
  rw [one_zsmul]
  rfl
def S1620ZSMulPointFormula : Prop :=
  ∀ n : ℤ, n ≠ 0 →
    ∃ h : Affine.Nonsingular pointedCurve.toAffine (smulX n) (smulY n),
      n • s1619Point = Affine.Point.some (smulX n) (smulY n) h
#check S1620ZSMulPointFormula
#check s1620OneZSMul
end LeanFormal.IUT.XiFPaper.S1620ZSMulPointInductionActual
end
