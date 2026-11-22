import tmp.sheaf.xif.paper.NativeSourceAssemblyPartial
import tmp.sheaf.xif.paper.NativeSourceAssemblyFinalPartial
import tmp.sheaf.xif.paper.NativeSplitReductionProof

/-!
# Split-field integration into NativeSourceAssembly

Integrates the actual multiplicative reduction/Tate comparison data with the
canonical Tate split criterion into the NativeSourceAssembly split field.

The actual part supplies multiplicative reduction at every native bad lift.
The split field is constructed conditionally from the exact missing criterion
NativeCanonicalTateSplitCriterion X.S. The same conditional criterion fills
the split slot of NativeSourceAssemblyMissingFields; the remaining missing
fields stay explicit. No arbitrary data/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeAssemblySplitIntegration

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitReductionProof
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeActual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartial
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFinalPartial

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Exact missing canonical Tate split criterion for the native input. -/
def MissingCanonicalTateSplitCriterion : Prop :=
  NativeCanonicalTateSplitCriterion X.S

/-- The split field of NativeSourceAssembly, from the canonical criterion. -/
def splitFieldOfCanonicalCriterion
    (h : MissingCanonicalTateSplitCriterion (l := l) X) :
    NativeSplitMultiplicativeAtLift X.S :=
  nativeSplitReduction_of_canonicalTateCriterion (T := X.S) h

/-- Actual multiplicative reduction remains available unconditionally. -/
def actualReductionData :
    ActualNativeReductionData (l := l) X.S :=
  actualNativeReductionData (T := X.S)

/-- Fill the split slot of NativeSourceAssemblyMissingFields from the
/-- canonical criterion, leaving the other missing fields explicit. -/
def nativeSourceAssemblyMissingFieldsOfCanonicalSplit
    (hsplit : MissingCanonicalTateSplitCriterion (l := l) X)
    (torsionGaps : NativeSourceTorsionGaps (A := X.S.arithmetic)
      (S := X.S.tuple.source) (C := X.S.clauseA) (B := X.S.clauseB) X.S.clauseC)
    (section : ExactSequenceSplittingSection (l := l) X.S)
    (cuspCount : Nat) (cuspCount_pos : 0 < cuspCount)
    (d7 : NativeD7Intake (SourceCompletion.ofSourceNative X.S))
    (cuspHyp : NativeCuspClauseHypotheses) :
    NativeSourceAssemblyMissingFields (l := l) X where
  split := splitFieldOfCanonicalCriterion (l := l) X hsplit
  torsionGaps := torsionGaps
  section := section
  cuspCount := cuspCount
  cuspCount_pos := cuspCount_pos
  d7 := d7
  cuspHyp := cuspHyp

/-- The conditionally integrated full assembly. -/
noncomputable def nativeSourceAssemblyOfCanonicalSplit
    (hsplit : MissingCanonicalTateSplitCriterion (l := l) X)
    (torsionGaps : NativeSourceTorsionGaps (A := X.S.arithmetic)
      (S := X.S.tuple.source) (C := X.S.clauseA) (B := X.S.clauseB) X.S.clauseC)
    (section : ExactSequenceSplittingSection (l := l) X.S)
    (cuspCount : Nat) (cuspCount_pos : 0 < cuspCount)
    (d7 : NativeD7Intake (SourceCompletion.ofSourceNative X.S))
    (cuspHyp : NativeCuspClauseHypotheses) :
    NativeSourceAssembly X.S :=
  nativeSourceAssemblyOfMissing (l := l) X
    (nativeSourceAssemblyMissingFieldsOfCanonicalSplit (l := l) X
      hsplit torsionGaps section cuspCount cuspCount_pos d7 cuspHyp)

#check MissingCanonicalTateSplitCriterion
#check splitFieldOfCanonicalCriterion
#check actualReductionData
#check nativeSourceAssemblyMissingFieldsOfCanonicalSplit
#check nativeSourceAssemblyOfCanonicalSplit
#check NativeSourceAssemblyMissingFields.split
#check nativeSourceAssemblyOfMissing

end LeanFormal.IUT.XiFPaper.NativeAssemblySplitIntegration

end
