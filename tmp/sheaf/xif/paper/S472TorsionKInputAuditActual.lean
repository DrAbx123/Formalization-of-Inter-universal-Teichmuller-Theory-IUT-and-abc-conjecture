import tmp.sheaf.xif.paper.S467KrootOrderControlAuditActual
import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual
import tmp.sheaf.xif.paper.S330QVFamilyRootCardActual
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

-- S472 audit: Torsion23Rational and K's l-torsion kernel definition are
-- actual, but repo has NO theorem deriving q-order parity or l | local
-- ramification index.  Exact missing inputs recorded.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S472TorsionKInputAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual 2*3-torsion rationality input (not a q-order parity theorem).
theorem torsion23_actual :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  S330QVFamilyRootCardActual.sourceTorsion23Rational_available T

-- Actual qVFamilyK order factorization from S438/S467.
theorem qVFamilyK_order_factorization_actual :
    (qVFamilyK T b).order =
      qVFamilyKRamificationIdx T b * (qVFamily T b).order :=
  qVFamilyK_order_factorization T b

-- Missing input 1: 2-torsion does not currently imply q-order parity.
def TwoTorsionToQOrderParityGap : Prop :=
  PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve →
    2 ∣ (qVFamily T b).order

-- Missing input 2: K/F local ramification index divisible by l.
def KLocalRamificationDivisibleByLGap : Prop :=
  l.value ∣ qVFamilyKRamificationIdx T b

-- Exact combined input needed for root order/ramification control.
structure S472RootOrderInput where
  two_dvd_order_F : 2 ∣ (qVFamily T b).order
  l_dvd_ramification : l.value ∣ qVFamilyKRamificationIdx T b
  twoL_dvd_order_K : (2 * l.value) ∣ (qVFamilyK T b).order
  root_valuation_control : Prop

def S472RootOrderInputRequired : Prop :=
  Nonempty (S472RootOrderInput T b)

-- Repo facts relevant to K: finite Galois kernel field and SL2 image are
-- actual; neither gives a local ramification-divisibility theorem.
#check InitialThetaSource.SourceClauseC.kernel_field_finite_galois
#check InitialThetaSource.SourceClauseC.image_spec

#check torsion23_actual
#check TwoTorsionToQOrderParityGap
#check KLocalRamificationDivisibleByLGap
#check S472RootOrderInputRequired

end LeanFormal.IUT.XiFPaper.S472TorsionKInputAuditActual

end