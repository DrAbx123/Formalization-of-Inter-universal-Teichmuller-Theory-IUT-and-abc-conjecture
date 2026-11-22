/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.TwoLthRootQVActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData

/-! # S319: completion 2l-th root from torsion23 data

The completion root problem is the actual unit qVUnit T b in
Completion((nativeBadLift T).lift b).  The source supplies

* Torsion23Rational T.arithmetic.curve (Clause C, 6-torsion rationality);
* an actual SourceTateComparisonWitness / qVFamily parameter at every bad lift.

This file records the exact missing implication

  Torsion23Rational -> Nonempty (NatRootSystem (qVUnit T b))

and the conditional construction of TwoLthRootData.  It does not use L,
does not fabricate a root, and does not assert an inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S319CompletionRootFromTorsion23Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual Torsion23Rational field supplied by the source. -/
theorem sourceTorsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  T.clauseC.torsion23_rational

/-- The actual q_v unit in the completion at b. -/
def completionQVUnit :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  qVUnit T b

/-- The exact missing implication: 6-torsion rationality supplies no
completion 2l-th root system for q_v. -/
def MissingCompletionRootFromTorsion23 : Prop :=
  PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve →
    Nonempty (NatRootSystem (qVUnit T b))

/-- Conditional construction: the missing implication gives the actual
completion root data. -/
theorem twoLthRootData_of_missingCompletionRoot
    (h : MissingCompletionRootFromTorsion23 (T := T) (b := b)) :
    Nonempty (TwoLthRootData T b) := by
  obtain ⟨R⟩ := h (sourceTorsion23Rational T)
  exact ⟨twoLthRootDataOfRootSystem T b R⟩

/-- The exact root-system gap is equivalent to the missing root implication
after the actual source torsion field is supplied. -/
theorem twoLRootExistenceGap_iff_missing :
    TwoLRootExistenceGap T b ↔
      Nonempty (NatRootSystem (qVUnit T b)) :=
  Iff.rfl

/-- The actual qVFamily parameter and source torsion are both available; the
root implication remains the missing datum. -/
theorem source_torsion_and_qVFamily_available :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve ∧
      (qVFamily T b).q ≠ 0 :=
  ⟨sourceTorsion23Rational T, (qVFamily T b).q_ne_zero⟩

/-- Exact missing completion-root datum, kept as a Prop (no inhabitant). -/
def MissingCompletionRootFromTorsion23Required : Prop :=
  MissingCompletionRootFromTorsion23 (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S319CompletionRootFromTorsion23Actual

end
