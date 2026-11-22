import tmp.sheaf.xif.paper.S1593ZSMulFieldActual
import tmp.sheaf.xif.paper.S1533UniversalPointActual
import tmp.sheaf.xif.paper.S1577CuspPsiEvalActual
/-! # S1594: nonsingular smulField — exact point-layer stop
S1593 gives smulField and the Z identities.  TauCeti's nonsingular_smulField
uses the point bridge n • universalPoint = smulField n; this tree has the
universal equation (S1533) but not the universal point nonsingularity nor the
point bridge.  The exact first missing point-layer objects are recorded below.
No fake coordinates. -/
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Jacobian
open scoped Polynomial.Bivariate
namespace LeanFormal.IUT.XiFPaper.S1594NonsingularSmulFieldActual
open WeierstrassCurve.Universal
open LeanFormal.IUT.XiFPaper.S1593ZSMulFieldActual
/-- Exact first missing: the universal point is nonsingular on pointedCurve. -/
def S1594UniversalPointNonsingular : Prop :=
  (pointedCurve.toAffine).Nonsingular universalX universalY
/-- Exact second missing: the point bridge n • universalPoint = smulField n. -/
def S1594ZSMulPointBridge (hns : S1594UniversalPointNonsingular) : Prop :=
  ∀ n : ℤ,
    (n • (Affine.Point.some universalX universalY hns)).toJacobian.point =
      ⟦smulField n⟧
/-- The S1593 nonsingular target, recorded for the consumer. -/
def S1594NonsingularSmulField : Prop :=
  S1593NonsingularSmulField
#check S1594UniversalPointNonsingular
#check S1594ZSMulPointBridge
#check S1594NonsingularSmulField
end LeanFormal.IUT.XiFPaper.S1594NonsingularSmulFieldActual
end
