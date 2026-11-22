import tmp.sheaf.xif.paper.NativeSplitMultiplicativeActual
import tmp.sheaf.n8.closure.NativeSplitProof
import tmp.sheaf.n8.closure.NativeSplitFromTate
import LeanFormal.IUT.IUTI.InitialTheta.TateComparisonBoundary
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

/-!
# Split-multiplicative reduction from the Tate comparison: exact status

At every native bad lift, clause B supplies an actual TateCurveComparison
and multiplicative reduction. Split multiplicative reduction is equivalent
(via the actual coordinate realization and invariance of split reduction
under variable change) to split multiplicative reduction of the canonical
Tate curve at the actual completed local field and q candidate. No source
theorem proves that canonical Tate split criterion for the actual q.

This file proves the equivalence/reduction and states the exact missing
criterion. It does not fabricate a split certificate. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.NativeSplitReductionProofAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitFromTate
open LeanFormal.IUT.N8Closure.NativeSplitProof
open LeanFormal.IUT.N8Closure.NativeBadLiftActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeActual

variable {l : PrimeGeFive}

/-- The exact split criterion: the actual canonical Tate curve at each native
/-- bad lift is split multiplicative on a minimal model. -/
def NativeCanonicalTateSplitCriterion
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  forall b : Bad (nativePlaceSelection T), CanonicalTateSplitAt T b

/-- Actual multiplicative reduction at every native bad lift, from the
/-- clause-B Tate comparison. -/
theorem nativeSplitReduction_multiplicative
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  (actualNativeReductionData T).multiplicative b

/-- The target split reduction is equivalent to the exact canonical Tate
/-- split criterion, using the actual coordinate realization and the
/-- variable-change invariance of split reduction. -/
theorem nativeSplitReduction_iff_canonicalTateCriterion
    (T : SourceNativeInitialThetaData.{0} l) :
    NativeSplitMultiplicativeAtLift T ↔
      NativeCanonicalTateSplitCriterion T := by
  unfold NativeCanonicalTateSplitCriterion
  exact nativeSplit_iff_canonicalTateSplit T

/-- Conditional proof of the target from the exact canonical Tate split
/-- criterion. -/
theorem nativeSplitReduction_of_canonicalTateCriterion
    (T : SourceNativeInitialThetaData.{0} l)
    (h : NativeCanonicalTateSplitCriterion T) :
    NativeSplitMultiplicativeAtLift T :=
  (nativeSplitReduction_iff_canonicalTateCriterion T).mpr h

/-- The exact missing split criterion, as a named proposition. -/
def MissingSplitCriterion
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  NativeCanonicalTateSplitCriterion T

/-- The actual clause-B Tate comparison alone supplies multiplicative but
/-- not split reduction; this is the exact gap. -/
theorem nativeSplitReduction_status
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :==
  nativeSplitReduction_multiplicative T b

#check NativeCanonicalTateSplitCriterion
#check nativeSplitReduction_iff_canonicalTateCriterion
#check nativeSplitReduction_of_canonicalTateCriterion
#check MissingSplitCriterion
#check nativeSplitReduction_status

end LeanFormal.IUT.N8Closure.NativeSplitReductionProofAdapted

end
