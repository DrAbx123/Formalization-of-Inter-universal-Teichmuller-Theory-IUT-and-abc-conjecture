import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap2ConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi Gap2 shape decomposition

Gap2 named estimate decomposed into its region/weight/theta/residual fields, with
the equivalence to `SNamed` exposed. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual

open LeanFormal.IUT.Objects.ABCBridgeGap2

structure Gap2Shape where
  regionVolume : ENNReal
  eps : Real
  weight : Real
  theta : Real
  D : Real
  named : SNamed regionVolume eps weight theta D

def Gap2Shape.toNamed (S : Gap2Shape) : Prop := S.named

theorem gap2_shape_named (S : Gap2Shape) :
    S.regionVolume ≤ ENNReal.ofReal ((1 + S.eps) * S.weight + S.theta + S.D) :=
  S.named

theorem gap2_shape_real (S : Gap2Shape)
    (hR : 0 ≤ (1 + S.eps) * S.weight + S.theta + S.D) :
    S.regionVolume.toReal ≤ (1 + S.eps) * S.weight + S.theta + S.D :=
  gap2_real_bound hR S.named

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGap2ShapeDecompositionActual

end
