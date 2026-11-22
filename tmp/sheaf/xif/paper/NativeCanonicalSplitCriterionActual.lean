import tmp.sheaf.xif.paper.NativeSplitReductionProof
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

/-!
# NativeCanonicalTateSplitCriterion: actual reduction/status

Task-683 attempts, for every native bad lift b,

  CanonicalTateSplitAt T b

i.e. split multiplicative reduction on a minimal model of the canonical Tate
curve at the actual comparison q and its completed local field.

Actual data:

* clause B supplies an actual SourceTateComparisonWitness and hence an actual
  TateCurveComparison at each native bad lift;
* NativeSplitReductionProof.nativeSplitReduction_multiplicative proves the
  actual multiplicative reduction at the completed curve for every b;
* NativeSplitReductionProof.nativeSplitReduction_iff_canonicalTateCriterion
  proves that the native split target is equivalent to the canonical Tate split
  criterion.

Missing: the split criterion itself.  The concrete theorem
TateCurveLocalReduction.canonicalCurve_hasSplitMultiplicativeReductionOnMinimalModel
proves split reduction for the fixed concrete canonicalCurve l over Z_l, not for
the arbitrary actual comparison q/completion.  No theorem transfers that fixed
curve result to CanonicalTateSplitAt T b, and the actual comparison only supplies
multiplicative reduction, not splitness.

This file constructs the conditional object and reports the exact missing
criterion.  No arbitrary certificate/axiom/sorry.  WRITE-ONLY; queue.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeCanonicalSplitCriterionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitProof
open LeanFormal.IUT.N8Closure.NativeSplitReductionProof

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Actual multiplicative reduction at every native bad lift, from the actual
clause-B Tate comparison. -/
theorem nativeMultiplicativeReductionActual
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  nativeSplitReduction_multiplicative T b

/-- The actual equivalence between the native split target and the canonical
Tate split criterion. -/
theorem nativeSplitTarget_iff_canonicalCriterion :
    NativeSplitMultiplicativeAtLift T ↔
      NativeCanonicalTateSplitCriterion T :=
  nativeSplitReduction_iff_canonicalTateCriterion T

/-- Conditional object-level construction: the canonical split criterion gives
the native split target. -/
theorem nativeSplitTarget_of_canonicalCriterion
    (h : NativeCanonicalTateSplitCriterion T) :
    NativeSplitMultiplicativeAtLift T :=
  nativeSplitReduction_of_canonicalTateCriterion T h

/-- Exact missing criterion, as a named proposition. -/
def MissingCanonicalTateSplitCriterion : Prop :=
  NativeCanonicalTateSplitCriterion T

/-- The exact missing object is exactly the criterion. -/
theorem missingCanonicalTateSplitCriterion_iff :
    MissingCanonicalTateSplitCriterion T ↔
      NativeCanonicalTateSplitCriterion T := Iff.rfl

/-- Actual status: multiplicative reduction is available at every bad lift; the
split criterion is not derived. -/
theorem nativeCanonicalSplitCriterionStatus
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) ∧
      (NativeCanonicalTateSplitCriterion T →
        NativeSplitMultiplicativeAtLift T) :=
  ⟨nativeMultiplicativeReductionActual T b,
    nativeSplitTarget_of_canonicalCriterion T⟩


end LeanFormal.IUT.XiFPaper.NativeCanonicalSplitCriterionActual
