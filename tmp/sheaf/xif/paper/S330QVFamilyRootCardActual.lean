/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import tmp.sheaf.xif.paper.TwoLthRootQVActual
import tmp.sheaf.xif.paper.S319CompletionRootFromTorsion23Actual

/-! # S330: G1 root descent from the QParameterTwoLRootCard

The repo already defines the frozen card

  QParameterTwoLRootCard l place parameter

with a nonzero completion root r and r^(2l) = parameter.q.  The same module
registers qParameterTwoLRootDescent as a pending obligation: no Kummer
surjectivity on principal units / Hensel input gives the descent to the
completion.

This file specializes the card to the actual qVFamily parameter and records:
* the exact missing card for qVFamily;
* a conditional construction of TwoLthRootData from an explicit card;
* the pending descent obligation status.

No root is fabricated, no L/transport is used, no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.S319CompletionRootFromTorsion23Actual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual place carrying qVFamily T b. -/
abbrev qVFamilyPlace : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The frozen 2l-th-root card specialized to the actual qVFamily parameter. -/
abbrev QVFamilyTwoLRootCard : Type :=
  QParameterTwoLRootCard l (qVFamilyPlace T b) (qVFamily T b)

/-- Exact missing card for the actual qVFamily: a completion root r with
r^(2l) = qVFamily.q. -/
def QVFamilyTwoLRootCardGap : Prop :=
  Nonempty (QVFamilyTwoLRootCard (T := T) (b := b))

/-- Exact missing Kummer/Hensel input, recorded as the same card gap.  The
upstream module documents the missing ingredients: Kummer surjectivity of the
2l-th power map on principal units and a Hensel/Kummer descent of the
algebraic-closure root to the completion. -/
def MissingKummerHenselInput : Prop :=
  QVFamilyTwoLRootCardGap (T := T) (b := b)

/-- The upstream descent obligation is still pending. -/
theorem qParameterTwoLRootDescent_pending :
    LeanFormal.IUT.Audit.qParameterTwoLRootDescent.status =
      LeanFormal.IUT.Audit.VerificationStatus.pending := rfl

/-- The actual source torsion statement is available. -/
theorem sourceTorsion23Rational_available :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  sourceTorsion23Rational T

/-- Conditional root unit from an explicit card. -/
noncomputable def qVUnitRootOfCard
    (C : QVFamilyTwoLRootCard (T := T) (b := b)) :
    (Completion (qVFamilyPlace T b))ˣ :=
  Units.mk0 C.root C.root_ne_zero

/-- The conditional root unit has the correct 2l-th power. -/
theorem qVUnitRootOfCard_pow
    (C : QVFamilyTwoLRootCard (T := T) (b := b)) :
    qVUnitRootOfCard T b C ^ twoLExponent l = qVUnit T b := by
  apply Units.ext
  change C.root ^ (2 * l.value) = (qVFamily T b).q
  exact C.root_pow

/-- Conditional TwoLthRootData from the explicit card. -/
noncomputable def twoLthRootDataOfCard
    (C : QVFamilyTwoLRootCard (T := T) (b := b)) :
    TwoLthRootData T b where
  root := qVUnitRootOfCard T b C
  root_pow := qVUnitRootOfCard_pow T b C

/-- The card gives the actual completion root data. -/
theorem twoLthRootData_nonempty_of_card
    (C : QVFamilyTwoLRootCard (T := T) (b := b)) :
    Nonempty (TwoLthRootData T b) :=
  ⟨twoLthRootDataOfCard T b C⟩

/-- The missing card is exactly the missing Kummer/Hensel input recorded here. -/
theorem missingKummerHenselInput_iff :
    MissingKummerHenselInput (T := T) (b := b) ↔
      QVFamilyTwoLRootCardGap (T := T) (b := b) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual

end
