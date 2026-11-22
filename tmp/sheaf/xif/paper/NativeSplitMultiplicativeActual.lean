import tmp.sheaf.n8.closure.NativeSplitFromTate
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.NativeBadLiftActual

/-!
# Actual native reduction data and the exact split-multiplicative gap

For the native source assembly, the actual curve-reduction data available
from clauses A/B are:
* stable reduction at every native bad lift;
* multiplicative reduction at every native bad lift (clause B);
* the actual clause-B Tate comparison at every native bad lift.

`NativeSplitMultiplicativeAtLift` itself is NOT constructed: neither the
Tate comparison nor the multiplicative-reduction theorem yields split
multiplicative reduction. This file constructs the actual reduction-data
object and records the exact missing split field. No arbitrary split
certificate/axiom/sorry. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitFromTate

variable {l : PrimeGeFive}

/-- Actual native reduction data available unconditionally. -/
structure ActualNativeReductionData
    (T : SourceNativeInitialThetaData.{0} l) where
  stable : forall b : Bad (nativePlaceSelection T),
    T.arithmetic.curve.HasStableReductionAt ((nativeBadLift T).lift b)
  multiplicative : forall b : Bad (nativePlaceSelection T),
    T.arithmetic.curve.HasMultiplicativeReductionAt ((nativeBadLift T).lift b)
  tateComparison : forall b : Bad (nativePlaceSelection T),
    TateCurveComparison T.arithmetic.curve ((nativeBadLift T).lift b)
      (nativeBadTateWitness T (nativeBadLift T) b).parameter

/-- The actual reduction-data object, constructed from clauses A/B and the
actual Tate witness. -/
noncomputable def actualNativeReductionData
    (T : SourceNativeInitialThetaData.{0} l) :
    ActualNativeReductionData T where
  stable := fun b =>
    T.clauseA.stable_reduction_nonarchimedean ((nativeBadLift T).lift b)
  multiplicative := fun b =>
    nativeTateComparison_multiplicative T b
  tateComparison := fun b => nativeTateComparison T b

/-- The exact missing split-multiplicative reduction field. -/
def MissingSplitMultiplicativeReduction
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  NativeSplitMultiplicativeAtLift T

/-- The missing field is exactly the assembly's split field. -/
theorem missingSplitMultiplicativeReduction_iff
    (T : SourceNativeInitialThetaData.{0} l) :
    MissingSplitMultiplicativeReduction T ↔ NativeSplitMultiplicativeAtLift T :=
  Iff.rfl

/-- Any split certificate gives the missing field; no such certificate is
constructed here. -/
def splitFieldOfMissing
    (T : SourceNativeInitialThetaData.{0} l)
    (h : MissingSplitMultiplicativeReduction T) :
    NativeSplitMultiplicativeAtLift T :=
  h

/-- The actual reduction data supplies stable and multiplicative reduction at
every native bad lift, but not split reduction. -/
theorem actualNativeReductionData_stable
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasStableReductionAt ((nativeBadLift T).lift b) :=
  (actualNativeReductionData T).stable b

theorem actualNativeReductionData_multiplicative
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt ((nativeBadLift T).lift b) :=
  (actualNativeReductionData T).multiplicative b

#check ActualNativeReductionData
#check actualNativeReductionData
#check MissingSplitMultiplicativeReduction
#check missingSplitMultiplicativeReduction_iff
#check splitFieldOfMissing
#check actualNativeReductionData_stable
#check actualNativeReductionData_multiplicative

end LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeActual

end
