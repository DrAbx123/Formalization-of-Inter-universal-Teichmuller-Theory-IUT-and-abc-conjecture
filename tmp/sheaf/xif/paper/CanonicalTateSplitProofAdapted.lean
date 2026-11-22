import tmp.sheaf.xif.paper.NativeCanonicalSplitCriterionActualAdapted
import tmp.sheaf.n8.closure.NativeSplitProof
import tmp.sheaf.n8.closure.NativeSplitFromTate
import LeanFormal.IUT.IUTI.InitialTheta.TateComparisonBoundary
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

/-!
# CanonicalTateSplitAt: proof attempt and exact missing criterion

Task-687 attempts, for the actual Tate comparison q/completion,

  CanonicalTateSplitAt T b:
    split multiplicative reduction on a minimal model of
    TateCurve.weierstrassCurve K q,

with K the completed local field and q the actual comparison q candidate.

Actual ingredients:

* actual clause-B Tate comparison at every native bad lift;
* actual multiplicative reduction at the completed curve;
* actual coordinate realization of the comparison;
* actual variable-change invariance of split-multiplicative reduction;
* actual equivalence
    NativeSplitMultiplicativeAtLift T <->
      (forall b, CanonicalTateSplitAt T b).

Not proved: the split criterion itself.  Clause B supplies a
TateCurveComparison with multiplicative reduction and coordinate realization,
but no splitness of the canonical Tate curve at the arbitrary actual q.  The
fixed concrete canonicalCurve l split theorem is not a theorem for the actual
comparison q.

This file proves the reductions and records the exact missing criterion.  No
arbitrary split certificate/axiom/sorry.  WRITE-ONLY; queue.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CanonicalTateSplitProofAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitProof
open LeanFormal.IUT.N8Closure.NativeSplitReductionProof
open LeanFormal.IUT.XiFPaper.NativeCanonicalSplitCriterionActualAdapted

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual clause-B multiplicative reduction at a native bad lift. -/
theorem tateComparison_multiplicativeAt
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  nativeMultiplicativeReductionActual T b

/-- The actual coordinate realization: the comparison curve is a variable
change of the canonical Tate curve at the actual q. -/
theorem tateComparison_coordinate_realization_actual
    (b : Bad (nativePlaceSelection T)) :
    let comparison := nativeTateComparison T b
    let K := NumberFieldFinitePlace.Completion comparison.finitePlaceInput.place
    let q := comparison.finitePlaceInput.qCandidate.q
    comparison.curveComparison.coordinateChange •
        TateCurve.weierstrassCurve K q =
      (comparison.finitePlaceInput.arithmetic.curve.baseChange K).curve :=
  fun _ _ => (nativeTateComparison T b).curveComparison.coordinate_realization

/-- Variable-change invariance of split multiplicative reduction on a minimal
model, as used by the reduction. -/
theorem splitCriterion_transport
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R W :=
  hasSplitMultiplicativeReductionOnMinimalModel_smul_iff R C W

/-- The exact missing criterion at a native bad lift. -/
def MissingCanonicalTateSplitAt
    (b : Bad (nativePlaceSelection T)) : Prop :=
  CanonicalTateSplitAt T b

/-- The all-lifts missing criterion. -/
def MissingCanonicalTateSplitAll : Prop :=
  forall b : Bad (nativePlaceSelection T), MissingCanonicalTateSplitAt T b

/-- Conditional construction of the native split target from the all-lifts
criterion, via the actual reduction theorem. -/
theorem nativeSplitTarget_of_missingCriterion
    (h : MissingCanonicalTateSplitAll T) :
    NativeSplitMultiplicativeAtLift T :=
  nativeSplitMultiplicativeAtLift_of_canonical T h

/-- Actual status: multiplicative reduction and the criterion equivalence are
available; the split criterion is the exact missing object. -/
theorem canonicalTateSplitStatus
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) ∧
      (NativeSplitMultiplicativeAtLift T ↔
        NativeCanonicalTateSplitCriterion T) :=
  ⟨tateComparison_multiplicativeAt T b,
    nativeSplitReduction_iff_canonicalTateCriterion T⟩

end LeanFormal.IUT.XiFPaper.CanonicalTateSplitProofAdapted
