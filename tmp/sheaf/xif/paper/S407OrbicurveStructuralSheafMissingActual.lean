import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual
import tmp.sheaf.xif.paper.S356RootStackActionGroupoidActual

-- S407: abandon the function-monoid O^tri surrogate.  The repo has actual
-- orbicurve/etale-stack/sign-action objects, but no structural sheaf
-- O^tri(T_x) and no q_v^{1/2l} section carrier.  Exact missing fields below.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S407OrbicurveStructuralSheafMissingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open LeanFormal.IUT.XiFPaper.S356RootStackActionGroupoidActual
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

universe u v

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Repo structural objects that do exist but do not define O^tri sections:
-- HyperbolicOrbicurve, EtaleStackOverField, OrbicurveSignAction.

structure OrbicurveStructuralSheafCarrierSpec where
  carrier : Type u
  [monoid : Monoid carrier]
  qSection : carrier
  rootSection : carrier
  qSection_toCompletion : carrier → Completion (qVFamilyPlace T b)
  qSection_toCompletion_q : qSection_toCompletion qSection = (qVFamily T b).q
  rootSection_pow : rootSection ^ (2 * l.value) = qSection
  mu2lAction : (rootsOfUnity (n (l := l)) (AC T b)) → carrier → carrier
  structuralSheafCondition : Prop

def OrbicurveStructuralSheafCarrierRequired : Prop :=
  Nonempty (OrbicurveStructuralSheafCarrierSpec.{0} T b)

-- The source tree contains only a pending obligation note for
-- qParameterTwoLRootDescent; no carrier/type is defined.

#check OrbicurveStructuralSheafCarrierSpec
#check OrbicurveStructuralSheafCarrierRequired

end LeanFormal.IUT.XiFPaper.S407OrbicurveStructuralSheafMissingActual

end