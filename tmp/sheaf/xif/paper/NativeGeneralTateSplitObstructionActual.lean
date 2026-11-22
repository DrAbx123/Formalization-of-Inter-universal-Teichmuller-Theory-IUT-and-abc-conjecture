import tmp.sheaf.xif.paper.NativeSplitSufficientConditionActual
import tmp.sheaf.n8.closure.NativeSplitFromTate
import tmp.sheaf.xif.paper.NativeSplitMultiplicativeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# General Tate split obstruction and per-b exact condition

The production TateCurve/LocalReduction API has:

* multiplicative reduction from the clause-B Tate comparison at every native
  bad lift;
* canonical split reduction only for the fixed concrete/canonical curve.

It has no constructor
  forall q, TateCurveComparison ... q -> HasSplitMultiplicativeReductionAt ...
for arbitrary qVFamily q.

This file records the exact per-b missing Tate split theorem and the precise
consumer reduction: the general split field reduces to that theorem, while the
concrete split witness is not used as a general native-q inhabitant.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeGeneralTateSplitObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeSplitFromTate
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeActual
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The exact per-b source theorem missing from the production TateCurve API:
the actual curve has split multiplicative reduction at the actual bad lift. -/
def NativeTateSplitTheoremAt
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) : Prop :=
  T.arithmetic.curve.HasSplitMultiplicativeReductionAt
    ((nativeBadLift T).lift b)

/-- The exact source theorem family. -/
def NativeTateSplitTheoremFamily : Prop :=
  ∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T),
    NativeTateSplitTheoremAt (l := l) T b

/-- Actual Tate comparison data at b (clause B), available unconditionally. -/
noncomputable def nativeTateComparisonAt
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    TateCurveComparison T.arithmetic.curve
      ((nativeBadLift T).lift b)
      (nativeBadTateWitness T (nativeBadLift T) b).parameter :=
  nativeTateComparison T b

/-- The actual Tate comparison supplies multiplicative reduction at b. -/
theorem nativeTateComparisonAt_multiplicative
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  nativeTateComparison_multiplicative T b

/-- The actual qVFamily Tate parameter at b. -/
noncomputable def nativeTateParameterAt
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    NumberFieldFinitePlace.FinitePlaceQCandidate
      ((nativeBadLift T).lift b) :=
  (nativeBadTateWitness T (nativeBadLift T) b).parameter

/-- The actual qVFamily Tate parameter is nonzero. -/
theorem nativeTateParameterAt_q_ne_zero
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    (nativeTateParameterAt (l := l) T b).q ≠ 0 :=
  (nativeTateParameterAt (l := l) T b).q_ne_zero

/-- The actual qVFamily Tate parameter has valuation less than one. -/
theorem nativeTateParameterAt_valuation_lt_one
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    (Valued.v (nativeTateParameterAt (l := l) T b).q :
      WithZero (Multiplicative Int)) < 1 :=
  (nativeTateParameterAt (l := l) T b).valuation_lt_one

/-- Exact per-b Tate split source certificate: the actual comparison plus the
missing split-reduction proof. This is an exact source object, not a theorem
restated as a proposition. -/
structure NativeTateSplitSourceCertificate
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) where
  comparison :
    TateCurveComparison T.arithmetic.curve
      ((nativeBadLift T).lift b)
      (nativeTateParameterAt (l := l) T b)
  coordinateChange :
    WeierstrassCurve.VariableChange
      (NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b))
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve
        (NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b))
        (nativeTateParameterAt (l := l) T b).q =
      (T.arithmetic.curve.baseChange
        (NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b))).curve
  splitReduction : NativeTateSplitTheoremAt (l := l) T b

/-- A certificate's split field is exactly the per-b Tate split theorem. -/
theorem NativeTateSplitSourceCertificate.split
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    (C : NativeTateSplitSourceCertificate (l := l) T b) :
    NativeTateSplitTheoremAt (l := l) T b :=
  C.splitReduction

/-- Exact missing certificate family. -/
def NativeTateSplitSourceCertificateRequired : Prop :=
  Nonempty ((b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) →
    NativeTateSplitSourceCertificate (l := l) T b)

/-- The exact missing theorem family yields the actual split-input family. -/
noncomputable def nativeSplitInputFamily_of_tateSplit
    (h : NativeTateSplitTheoremFamily (l := l) T) :
    NativeSplitInputFamily (l := l) T :=
  fun b =>
    { qCandidate :=
        (nativeBadTateWitness T (nativeBadLift T) b).parameter
      splitReduction := h b }

/-- Consumer: the assembly split field from the exact Tate split theorem. -/
theorem nativeSplitMultiplicativeAtLift_of_tateSplit
    (h : NativeTateSplitTheoremFamily (l := l) T) :
    NativeSplitMultiplicativeAtLift T :=
  nativeSplitMultiplicativeAtLift_of_inputFamily
    (l := l) T (nativeSplitInputFamily_of_tateSplit (l := l) T h)

/-- Exact per-b condition is not a concrete-q substitute: the concrete split
witness lives over the concrete Gaussian data, not over arbitrary native T. -/
def NativeGeneralQSplitSourceMissing : Prop :=
  NativeTateSplitTheoremFamily (l := l) T

/-- The missing source gap is exactly the family of per-b Tate split theorems. -/
theorem nativeGeneralQSplitSourceMissing_iff :
    NativeGeneralQSplitSourceMissing (l := l) T ↔
      NativeTateSplitTheoremFamily (l := l) T :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.NativeGeneralTateSplitObstructionActual

end
