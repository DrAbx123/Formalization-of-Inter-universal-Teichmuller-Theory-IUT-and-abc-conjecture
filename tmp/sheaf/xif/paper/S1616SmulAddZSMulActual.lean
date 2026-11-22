import tmp.sheaf.xif.paper.S1615AddXAddYFromDraftActual
import tmp.sheaf.xif.paper.S1600RelatorNormalFormActual
import tmp.sheaf.xif.paper.S1601ZSMulPointFormulaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1616SmulAddZSMulActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
open LeanFormal.IUT.XiFPaper.S1605PointedCurveCoeffActual
open LeanFormal.IUT.XiFPaper.S1606SlopeDoublingActual
open LeanFormal.IUT.XiFPaper.S1612ZSMulPointFinalActual
open LeanFormal.IUT.XiFPaper.S1615AddXAddYFromDraftActual

#check s1615_addX_smul_one_smul_one
#check s1615_addY_smul_one_smul_one
#check smulX_sub_sub_smulX_add
#check smulX_sub_smulX
#check s1600RelatorNormalForm
#check s1605_smulY_sub_negY
#check S1612SmulXAdd
#check S1612SmulYAddSubNegY

/-- Exact chord X target. -/
def S1616SmulXAdd : Prop := S1612SmulXAdd

/-- Exact chord Y target. -/
def S1616SmulYAddSubNegY : Prop := S1612SmulYAddSubNegY

end LeanFormal.IUT.XiFPaper.S1616SmulAddZSMulActual
end