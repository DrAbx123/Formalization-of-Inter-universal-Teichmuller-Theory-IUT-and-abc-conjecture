import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.NativeSourceReductionActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic

/-!
# Native split multiplicative reduction at the bad lifts

The target is

  NativeSplitMultiplicativeAtLift T
    = forall b, T.arithmetic.curve.HasSplitMultiplicativeReductionAt
        ((nativeBadLift T).lift b).

Clause B gives, for each bad lift p, an actual TateCurveComparison

  W : TateCurveComparison T.arithmetic.curve p qVFamily

with

  W.coordinateChange • TateCurve.weierstrassCurve (Completion p) q
    = (T.arithmetic.curve.baseChange (Completion p)).curve.

Split multiplicative reduction is invariant under variable change
(hasSplitMultiplicativeReductionOnMinimalModel_smul_iff).  Therefore the
actual curve has split multiplicative reduction at p provided the canonical
Tate curve

  TateCurve.weierstrassCurve (Completion p) q

has split multiplicative reduction over the completed valuation ring.

The tree does not currently prove this canonical Tate split-reduction theorem
for a general contracting q.  The exact missing theorem is recorded as
CanonicalTateSplitReduction; the actual implication from it to
NativeSplitMultiplicativeAtLift is proved, with no fake canonical model.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeSplitMultiplicativeAtLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual Tate comparison at the bad lift. -/
noncomputable def nativeSplitTateComparison :
    TateCurveComparison T.arithmetic.curve
      ((nativeBadLift T).lift b) (qVFamily T b) :=
  (nativeBadTateWitness T (nativeBadLift T) b).comparison

/-- The canonical Tate curve at the bad lift and its actual q. -/
noncomputable def canonicalTateCurveAtBad :
    WeierstrassCurve (Completion ((nativeBadLift T).lift b)) :=
  TateCurve.weierstrassCurve
    (Completion ((nativeBadLift T).lift b)) (qVFamily T b).q

/-- Exact missing theorem: the canonical Tate curve has split multiplicative
reduction over the completed valuation ring. -/
def CanonicalTateSplitReduction : Prop :=
  HasSplitMultiplicativeReductionOnMinimalModel
    (CompletionIntegers ((nativeBadLift T).lift b))
    (canonicalTateCurveAtBad T b)

/-- Actual conditional implication: canonical Tate split reduction gives split
multiplicative reduction of the actual curve at the bad lift, using the actual
Tate comparison's variable change. -/
theorem nativeSplitAt_of_canonicalTateSplit
    (hcanon : CanonicalTateSplitReduction T b) :
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b) := by
  let W := nativeSplitTateComparison T b
  change HasSplitMultiplicativeReductionOnMinimalModel
    (CompletionIntegers ((nativeBadLift T).lift b))
    ((T.arithmetic.curve.baseChange
      (Completion ((nativeBadLift T).lift b))).curve)
  rw [← W.realizesCurve]
  exact (hasSplitMultiplicativeReductionOnMinimalModel_smul_iff
    (R := CompletionIntegers ((nativeBadLift T).lift b))
    W.coordinateChange (canonicalTateCurveAtBad T b)).mpr hcanon

/-- The exact missing canonical Tate split-reduction theorem, for all bad
lifts. -/
def CanonicalTateSplitReductionGap : Prop :=
  ∀ b : Bad (nativePlaceSelection T), CanonicalTateSplitReduction T b

/-- The target follows from the exact canonical Tate split-reduction gap. -/
theorem nativeSplitMultiplicativeAtLift_of_canonicalGap
    (h : CanonicalTateSplitReductionGap T) :
    NativeSplitMultiplicativeAtLift T :=
  fun b => nativeSplitAt_of_canonicalTateSplit T b (h b)

/-- The exact conditional form: the only missing input is the canonical Tate
split-reduction theorem. -/
theorem nativeSplitMultiplicativeAtLift_of_canonical
    (h : ∀ b : Bad (nativePlaceSelection T), CanonicalTateSplitReduction T b) :
    NativeSplitMultiplicativeAtLift T :=
  nativeSplitMultiplicativeAtLift_of_canonicalGap T h

end LeanFormal.IUT.XiFPaper.NativeSplitMultiplicativeAtLiftActual

end
