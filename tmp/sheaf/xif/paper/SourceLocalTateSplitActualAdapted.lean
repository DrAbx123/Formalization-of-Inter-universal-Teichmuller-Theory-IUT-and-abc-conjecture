import LeanFormal.IUT.IUTI.InitialTheta.SourceLocalTateBoundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.n8.closure.NativeSplitProof
import tmp.sheaf.n8.closure.NativeSplitFromTate
import tmp.sheaf.n8.closure.NativeInput

/-!
# Extract actual split reduction from the source local Tate boundary

Task-697 inspects the actual SourceNativeInitialThetaData T and its clauses for
a SourceLocalTateBoundary / splitReduction / localSplitReduction witness.

Findings:

* SourceLocalTateBoundary (SourceLocalTateBoundary.lean:24-37) has exactly the
  wanted fields: comparison : InitialThetaTateComparison, splitReduction :
  HasSplitMultiplicativeReductionAt, localSplitReduction :
  HasSplitMultiplicativeReductionOnMinimalModel, finiteLabels.
* SourceNativeInitialThetaData T does NOT contain a SourceLocalTateBoundary
  field.  Its ClauseB supplies only:
    - multiplicative_over_bad;
    - q_comparison : Nonempty (SourceTateComparisonWitness A p);
    - residue_characteristic_prime_to_l.
  No splitReduction/localSplitReduction field occurs in ClauseB or the native
  tuple.
* NativeSplitProof.CanonicalTateSplitAt T b is exactly the missing actual-q
  split criterion; it is not extracted from the source local boundary because
  that boundary is absent from T.

This file constructs the actual boundary projections when a
SourceLocalTateBoundary is supplied, and records the exact missing source
boundary field for T.  No arbitrary witness/axiom/sorry.  WRITE-ONLY; queue.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SourceLocalTateSplitActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeSplitProof
open LeanFormal.IUT.N8Closure.NativeSplitFromTate

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-! ## 1. Actual boundary projections, when a boundary is supplied -/

/-- The actual split reduction field of a supplied source local Tate boundary. -/
theorem sourceLocalTateBoundary_split
    (B : SourceLocalTateBoundary.{0} l) :
    B.comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      B.comparison.finitePlaceInput.place :=
  B.splitReduction

/-- The actual local split-on-minimal-model field of a supplied boundary. -/
theorem sourceLocalTateBoundary_localSplit
    (B : SourceLocalTateBoundary.{0} l) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (NumberFieldFinitePlace.CompletionIntegers
        B.comparison.finitePlaceInput.place)
      ((B.comparison.finitePlaceInput.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion
          B.comparison.finitePlaceInput.place)).curve) :=
  B.localSplitReduction

/-- The actual finite-label certificate field of a supplied boundary. -/
theorem sourceLocalTateBoundary_labels
    (B : SourceLocalTateBoundary.{0} l) :
    FiniteCyclicQuotient.IntegerCertificate l.value :=
  B.finiteLabels

/-! ## 2. What T actually provides -/

/-- Clause B supplies an actual Tate comparison witness at every bad lift, but
not a split reduction field. -/
noncomputable def clauseBComparisonWitness
    (b : Bad (nativePlaceSelection T)) :
    SourceTateComparisonWitness T.arithmetic ((nativeBadLift T).lift b) :=
  Classical.choice
    (T.clauseB.q_comparison ((nativeBadLift T).lift b)
      (by
        rw [(nativeBadLift T).lift_comap b]
        exact b.2))

/-- The actual multiplicative reduction obtained from the clause-B comparison. -/
theorem clauseBMultiplicative
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  T.clauseB.multiplicative_over_bad ((nativeBadLift T).lift b)
    (by
      rw [(nativeBadLift T).lift_comap b]
      exact b.2)

/-! ## 3. Exact missing source boundary field -/

/-- Exact missing source boundary: a SourceLocalTateBoundary (or at least its
two split-reduction fields) is not a field of T. -/
def MissingSourceLocalTateBoundary (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (SourceLocalTateBoundary.{0} l)

/-- The exact missing split field for the actual-q criterion. -/
def MissingActualQSplitField (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  NativeCanonicalTateSplitCriterion T

/-- The source local boundary, if supplied, gives its own split fields; it does
not identify them with the native comparison q without an additional
identification. -/
theorem sourceLocalTateBoundary_gives_split
    (B : SourceLocalTateBoundary.{0} l) :
    B.comparison.finitePlaceInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      B.comparison.finitePlaceInput.place :=
  sourceLocalTateBoundary_split B

/-- Exact status: T supplies multiplicative reduction and comparison witnesses;
the split-reduction field / actual-q split criterion is missing. -/
theorem sourceLocalTateSplitStatus
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) ∧
      (MissingActualQSplitField T ↔
        NativeCanonicalTateSplitCriterion T) :=
  ⟨clauseBMultiplicative T b, Iff.rfl⟩

end LeanFormal.IUT.XiFPaper.SourceLocalTateSplitActualAdapted
