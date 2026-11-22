import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual
import tmp.sheaf.xif.paper.S3133M2bClauseBDescentActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import tmp.sheaf.xif.paper.S3130QCSourceActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

/-!
# M2b attack: clause-B q data, Tate-q identification spec, reduction (component)

COMPONENT, not a paper object.  Named consumers: task-67/lattice R1,
mainline M2 registry.

Source: IUT I, Definition 3.1, (b), (c) (bad place selection and the chosen
q_v/Tate parameter data); IUT I, Example 3.2, (iv); IUT II, Remark 2.5.1, (i);
IUT III, Definition 3.8, (i), p. 112-113.

WHAT IS PROVED HERE:
* the actual clause-B q at a bad place is literally the chosen parameter of the
  actual SourceTateComparisonWitness (S3133M2b_clauseB_witness): definitional
  restatement of S3133M2_clauseB_q_parameter against
  T.clauseB.q_comparison;
* the Batch-A Q_C source q is the same clause-B parameter
  (S3133M2b_QCSource_qV): restatement of
  S3133M2_QCSource_qV_eq_clauseB for the concrete source data;
* M2b follows from the shrunk Gaussian q-parameter match
  (S3133GaussianClauseBDescent_of_atBase, PROVED) and the two together are
  equivalent given a canonical Gaussian q
  (S3133GaussianQParameterMatchAtBase_of_ClauseBDescent_and_canonicalQ,
  PROVED in S3133M2bClauseBDescentActual).

EXACT MISSING (insufficiency): the generic SourceClauseB structure
(SourceDefinition31Quantifiers) at each bad F-place provides only
Nonempty (SourceTateComparisonWitness A p), where the witness carries an
arbitrary FinitePlaceQCandidate p and a TateCurveComparison; it asserts NO norm
value.  The value 1/5 therefore has to come from the paper's chosen q_v
(IUT I, Definition 3.1(b), Example 3.2(iv); the D4 boundary): it is not derivable
from the generic clause structure or from the actual bad-place q data.  The
minimal exact-missing specification is
S3133M2bTateQIdentification below: a chosen Gaussian base q of norm 1/5 together
with the clause-B descent identification.  The norm value 1/5 of the chosen q can
itself be taken from an actual Gaussian Tate parameter once M2a's base norm
computation is closed.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133M2bAttackActual

local instance s3133M2bGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3130QCSourceActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133M2BaseQReductionActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.S3133M2bClauseBDescentActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual clause-B q is the chosen parameter of the actual Tate comparison
witness (definitional restatement). -/
theorem S3133M2b_clauseB_witness (b : Bad (nativePlaceSelection T)) :
    qVFamily T b =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter :=
  S3133M2_clauseB_q_parameter T b

/-- The Q_C source q is the same clause-B parameter. -/
theorem S3133M2b_QCSource_qV (b : Bad (nativePlaceSelection T))
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).qV =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter :=
  S3133M2_QCSource_qV_eq_clauseB T b h

/-- The minimal exact-missing specification for M2b: a chosen Gaussian base q
of norm 1/5 together with the clause-B/Tate-q descent identification (D4).
The descent field is the exact missing content (no norm value is asserted by the
generic SourceClauseB structure). -/
structure S3133M2bTateQIdentification where
  /-- chosen base q in the canonical Gaussian completion -/
  q : Completion concreteGaussianFivePlace
  q_norm : ‖q‖ = ((5 : Real)⁻¹)
  /-- exact missing: the clause-B q at every bad place above 5 has the chosen
  q's norm (the Tate-q identification, IUT I Definition 3.1(b), Example
  3.2(iv); the D4 boundary) -/
  descent : ∀ b : Bad (nativePlaceSelection T),
    (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
      ‖(qVFamily T b).q‖ = ‖q‖

/-- Exact-missing propagation: the Tate-q identification spec yields the M2b
clause-B descent. -/
theorem S3133GaussianClauseBDescent_of_tateQIdentification
    (S : S3133M2bTateQIdentification T) :
    S3133GaussianClauseBDescent T := by
  intro b h5 q' _hq'
  rw [S.descent b h5, S.q_norm]

end LeanFormal.IUT.XiFPaper.S3133M2bAttackActual
