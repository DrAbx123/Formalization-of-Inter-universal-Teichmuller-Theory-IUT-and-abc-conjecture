import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual
import tmp.sheaf.xif.paper.S1617SmulAddFromDraftActual
import tmp.sheaf.xif.paper.S1615AddXAddYFromDraftActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1618ZSMulPointFinalActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual
open LeanFormal.IUT.XiFPaper.S1617SmulAddFromDraftActual

#check s1615_addX_smul_one_smul_one
#check s1615_addY_smul_one_smul_one
#check s1617_smulX_add
#check s1617_smulY_add_sub_negY
#check s1617_SmulXAdd
#check s1617_SmulYAddSubNegY

/-- Exact missing point-layer target.  The local tree has the affine
coordinates smulX/smulY but no universal distinguished affine point
Affine.point and no point-level zsmul recursion API. -/
structure S1618PointLayerRequired where
  point : (pointedCurve.toAffine).Point
  xCoord_eq : Affine.Point.xCoord point = some (smulX 1)
  yCoord_eq : Affine.Point.yCoord point = some (smulY 1)

end LeanFormal.IUT.XiFPaper.S1618ZSMulPointFinalActual
end