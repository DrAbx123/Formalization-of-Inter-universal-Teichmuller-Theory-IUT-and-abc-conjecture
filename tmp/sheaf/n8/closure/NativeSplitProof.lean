import tmp.sheaf.n8.closure.NativeSplitFromTate
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.TateCurveLocalReduction
import LeanFormal.IUT.IUTI.InitialTheta.TateComparisonBoundary
import Mathlib.Tactic

/-!
# Deep attempt: split-multiplicative reduction at the native lift

The actual clause-B Tate comparison supplies, at each native bad lift,
a coordinate change

  C • TateCurve(q) = (curve.baseChange K).curve,

where K is the completed local field. Split multiplicative reduction on a
minimal model is invariant under variable changes. Therefore the native
split target is exactly the split assertion for the canonical Tate curve at
the actual q, at the same completion. This is a genuine reduction, not a
split proof.

The missing primitive is the canonical Tate split theorem for the actual
q candidate (the existing concrete canonicalCurve split theorem is for the
fixed concrete canonical curve, not for the actual q). No fake split is
asserted. No lake/compile is run in this task.

Status: conditional reduction + exact primitive. Target not proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.N8Closure.NativeSplitProof

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeSplitFromTate
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive}

/-- The canonical Tate split primitive at an actual Tate comparison: split
multiplicative reduction on a minimal model of the canonical Tate curve at
the comparison's completed local field. This is the exact remaining source
theorem needed to derive the native split target. -/
def CanonicalTateSplitAt
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  let place := (nativeBadLift T).lift b
  let prime := NumberFieldFinitePlace.underlyingPrime place
  let K := NumberFieldFinitePlace.Completion place
  let q := (nativeBadTateWitness T (nativeBadLift T) b).parameter.q
  HasSplitMultiplicativeReductionOnMinimalModel
    (prime.adicCompletionIntegers T.arithmetic.F)
    (TateCurve.weierstrassCurve K q)

/-- The coordinate realization of the actual Tate comparison, re-stated for
the canonical Tate curve and the completed actual curve. -/
theorem tateComparison_coordinate_realization
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    let place := (nativeBadLift T).lift b
    let K := NumberFieldFinitePlace.Completion place
    let q := (nativeBadTateWitness T (nativeBadLift T) b).parameter.q
    (nativeTateComparison T b).coordinateChange •
        TateCurve.weierstrassCurve K q =
      (T.arithmetic.curve.baseChange K).curve :=
  (nativeTateComparison T b).coordinate_realization

/-- Split multiplicative reduction on a minimal model is invariant under
variable change. This is the actual geometric input used by the reduction. -/
theorem splitMultiplicativeReduction_smul_iff
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R W :=
  hasSplitMultiplicativeReductionOnMinimalModel_smul_iff R C W

/-- If the canonical Tate curve at the actual q is split on a minimal model,
then the native split target follows for that bad lift. This uses the actual
coordinate realization and the variable-change invariance above. -/
theorem nativeSplitMultiplicativeAtLift_of_canonical
    (T : SourceNativeInitialThetaData.{0} l)
    (h : ∀ b : Bad (nativePlaceSelection T), CanonicalTateSplitAt T b) :
    NativeSplitMultiplicativeAtLift T := by
  intro b
  let place := (nativeBadLift T).lift b
  let prime := NumberFieldFinitePlace.underlyingPrime place
  let K := NumberFieldFinitePlace.Completion place
  let q := (nativeBadTateWitness T (nativeBadLift T) b).parameter.q
  have hsplit := h b
  change HasSplitMultiplicativeReductionOnMinimalModel
    (prime.adicCompletionIntegers T.arithmetic.F)
    ((T.arithmetic.curve.baseChange K).curve)
  rw [← (nativeTateComparison T b).coordinate_realization]
  exact (splitMultiplicativeReduction_smul_iff
    (nativeTateComparison T b).coordinateChange
    (TateCurve.weierstrassCurve K q)).mpr hsplit

/-- Exact reduction: the native split target is equivalent to the canonical
Tate split primitive at every native bad lift. -/
theorem nativeSplit_iff_canonicalTateSplit
    (T : SourceNativeInitialThetaData.{0} l) :
    NativeSplitMultiplicativeAtLift T ↔
      (∀ b : Bad (nativePlaceSelection T), CanonicalTateSplitAt T b) := by
  constructor
  · intro h b
    let place := (nativeBadLift T).lift b
    let prime := NumberFieldFinitePlace.underlyingPrime place
    let K := NumberFieldFinitePlace.Completion place
    let q := (nativeBadTateWitness T (nativeBadLift T) b).parameter.q
    unfold CanonicalTateSplitAt
    have hb := h b
    change HasSplitMultiplicativeReductionOnMinimalModel
      (prime.adicCompletionIntegers T.arithmetic.F)
      ((T.arithmetic.curve.baseChange K).curve) at hb
    have hEq : (T.arithmetic.curve.baseChange K).curve =
        (nativeTateComparison T b).coordinateChange •
          TateCurve.weierstrassCurve K q :=
      ((nativeTateComparison T b).coordinate_realization).symm
    have hcanon : HasSplitMultiplicativeReductionOnMinimalModel
        (prime.adicCompletionIntegers T.arithmetic.F)
        ((nativeTateComparison T b).coordinateChange •
          TateCurve.weierstrassCurve K q) := hEq ▸ hb
    exact (splitMultiplicativeReduction_smul_iff
      (nativeTateComparison T b).coordinateChange
      (TateCurve.weierstrassCurve K q)).mp hcanon
  · exact nativeSplitMultiplicativeAtLift_of_canonical T

/- Exact missing primitive: CanonicalTateSplitAt T b for the actual q. The
concrete theorem canonicalCurve_hasSplitMultiplicativeReductionOnMinimalModel
only handles the fixed concrete canonical curve, not an arbitrary actual q,
so it cannot be substituted. No split proof or axiom is introduced here. -/

#check CanonicalTateSplitAt
#check nativeSplitMultiplicativeAtLift_of_canonical
#check nativeSplit_iff_canonicalTateSplit

end LeanFormal.IUT.N8Closure.NativeSplitProof

end