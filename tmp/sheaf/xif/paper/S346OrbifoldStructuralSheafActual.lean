import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual

/-! # S346: orbifold structural sheaf O^tri(T_x) / O^triangleright carrier spec

Repo search: the only O^{tri}(T_x) material is descriptive/obligation text in
SourcePlaceQParameterUniformization (qParameterTwoLRootDescent, status pending)
and SourceDefinition31D4TateQIdentification.  No actual carrier type for the
orbifold structural sheaf / root stack O^triangleright(T_x), and no q_v^{1/2l}
section in that carrier, is defined in the repo.

This file gives the minimal exact missing spec, with no carrier inhabitant.
The completion card is impossible (S342), so the missing carrier must be a
non-completion, non-L object; the spec records that requirement as a Prop.

No L, no fake carrier, no fake root, no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
open LeanFormal.IUT.XiFPaper.S319CompletionRootFromTorsion23Actual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Minimal exact missing spec for the orbifold structural sheaf / root-stack
carrier O^tri(T_x) and its q_v^{1/2l} section.

The carrier is deliberately not identified with the completion or with L; the
paper object is a separate orbifold/root-stack carrier.  The fields are the
minimal data needed by the paper section: a monoid carrier, a q-section, a
root section whose 2l-th power is the q-section, a name relation to the actual
qVFamily q, and the structural-sheaf condition (kept as a Prop because the
repo does not define O^tri). -/
structure OrbifoldStructuralSheafCarrierSpec
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  carrier : Type u
  [monoid : Monoid carrier]
  qSection : carrier
  rootSection : carrier
  qSection_toCompletion : carrier → Completion (qVFamilyPlace T b)
  qSection_toCompletion_q : qSection_toCompletion qSection = (qVFamily T b).q
  rootSection_pow : rootSection ^ (2 * l.value) = qSection
  structuralSheafCondition : Prop

/-- Exact missing carrier/section datum. -/
def OrbifoldStructuralSheafRootSectionRequired : Prop :=
  Nonempty (OrbifoldStructuralSheafCarrierSpec.{u} T b)

/-- The completion root card is impossible (S342), so no completion/L carrier
can satisfy the paper root-section requirement. -/
theorem completionCarrier_cannot_supply_root :
    ¬ Nonempty (NatRootSystem (qVUnit T b)) :=
  natRootSystem_impossible T b

/-- The actual source torsion statement is available; the missing datum is the
orbifold carrier, not the 6-torsion statement. -/
theorem sourceTorsion23Rational_available :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  sourceTorsion23Rational T


end LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual

end
