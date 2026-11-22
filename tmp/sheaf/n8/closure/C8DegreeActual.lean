import tmp.sheaf.n8.closure.SourceDegreeComparison
import tmp.sheaf.n8.closure.SourceDegreeComparisonIQ
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# C8 actual arithmetic degree: profile donor vs C8 normalized log-volume

The production determinant/degree donor is the actual `profileArithmeticDegree`
on the C6 lambda profile.  This file defines the actual arithmetic degree of
the weighted determinant tensor power from C6 data and compares it with the
actual C8 normalized log-volume `B.normalizedLogVolume B.hull`.

No free Real parameter is introduced.  The comparison to the C8 normalized
log-volume is the exact missing (Ob3-3) statement and is a named sorry.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8Closure.C8
open LeanFormal.IUT.N8Closure.C8IQ

namespace LeanFormal.IUT.N8Closure.C8DegreeActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {iota : Type v} [Fintype iota] {V : iota → Type w}
  {places : (i : iota) → V i → FinitePlaceAtPrime K p}
  {tuple : (i : iota) → V i}
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
  [Measure.IsAddHaarMeasure mu]

/-- The actual C6 lambda weight profile. -/
def actualLambdaProfile (C6 : PaperNormalizedVolumeData places tuple mu) (i : iota) : ℝ :=
  C6.lambdaData.lambda i

/-- Actual arithmetic degree of `det^{tensor M}` from the production
`profileArithmeticDegree` donor and the actual C6 tuple denominator `M`. -/
def actualArithmeticDegree (C6 : PaperNormalizedVolumeData places tuple mu) : ℝ :=
  profileArithmeticDegree ((C6.tupleWeights.denominator : ℕ) •
    (actualLambdaProfile (C6 := C6) - fun _ => 0))

/-- The actual arithmetic degree is `M` times the sum of the C6 lambda
weights, with `M` the actual C6 tuple denominator. -/

theorem actualArithmeticDegree_eq_tupleDenominator_mul_sum
    (C6 : PaperNormalizedVolumeData places tuple mu) :
    actualArithmeticDegree C6 =
      (C6.tupleWeights.denominator : ℝ) * ∑ i : iota, C6.lambdaData.lambda i := by
  unfold actualArithmeticDegree actualLambdaProfile
  rw [profileArithmeticDegree_nsmul]
  congr 1
  unfold profileArithmeticDegree
  simp

/-- The C8 relative determinant degree is exactly the C8 actual arithmetic
degree. -/
theorem c8RelativeDetDegree_eq_actualArithmeticDegree
    (C6 : PaperNormalizedVolumeData places tuple mu) :
    LeanFormal.IUT.N8Closure.C8.c8RelativeDetDegree
      (V := V) (places := places) (tuple := tuple) C6 =
      actualArithmeticDegree (C6 := C6) := rfl

/-- Exact residual of the missing (Ob3-3) C8 degree/log-volume comparison. -/
def C8ActualDegreeResidual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (B : C6ActualIQData places tuple mu) : Prop :=
  actualArithmeticDegree C6 = B.normalizedLogVolume B.hull

/-- Conditional consumer: the residual is exactly the missing (Ob3-3) identity. -/
theorem actualArithmeticDegree_eq_c8NormalizedLogVolume_of_residual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (B : C6ActualIQData places tuple mu)
    (h : C8ActualDegreeResidual C6 B) :
    actualArithmeticDegree C6 = B.normalizedLogVolume B.hull := h

end LeanFormal.IUT.N8Closure.C8DegreeActual

end
