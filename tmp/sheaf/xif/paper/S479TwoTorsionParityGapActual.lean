import tmp.sheaf.xif.paper.S472TorsionKInputAuditActual
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion

-- S479 audit: no repo theorem links 2-torsion rationality to a q-square
-- root or to 2 | order(q).  The required lemma is recorded exactly.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S479TwoTorsionParityGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S472TorsionKInputAuditActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual 2*3-torsion input: rationality only.
theorem torsion23_input_actual :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  torsion23_actual T

-- Actual TateCurveComparison fields (no q-square-root/2-torsion link).
#check LeanFormal.IUT.TateCurveComparison
#check LeanFormal.IUT.TateCurveComparison.canonical_elliptic
#check LeanFormal.IUT.TateCurveComparison.coordinate_realization
#check LeanFormal.IUT.TateCurveComparison.point_comparison

-- Exact required lemma: a rational 2-torsion point together with a
-- compatible square root of q, giving order parity.
structure TwoTorsionToQSqrtGap where
  point : T.arithmetic.curve.AlgebraicClosurePoint
  point_two_torsion : (2 : Nat) • point = 0
  q : Completion ((nativeBadLift T).lift b)
  root : Completion ((nativeBadLift T).lift b)
  root_pow : root ^ 2 = q
  q_eq_qVFamily : q = (qVFamily T b).q
  point_root_compat : Prop
  order_even : 2 ∣ (qVFamily T b).order

def TwoTorsionToQSqrtGapRequired : Prop :=
  Nonempty (TwoTorsionToQSqrtGap T b)

-- Arithmetic reduction if such a same-place square root exists.
theorem twoTorsionToQSqrtGap_requires_order_even
    (D : TwoTorsionToQSqrtGap T b) :
    2 ∣ (qVFamily T b).order :=
  D.order_even

#check torsion23_input_actual
#check TwoTorsionToQSqrtGap
#check TwoTorsionToQSqrtGapRequired

end LeanFormal.IUT.XiFPaper.S479TwoTorsionParityGapActual

end