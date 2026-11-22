import tmp.sheaf.n8.closure.C8DegreeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import Mathlib

/-!
# C8 determinant/degree donor search

Production donor: profileArithmeticDegree (finite sum of a realified degree
profile) and the det-tensor-power bookkeeping lemmas in
HullDeterminantLogVolumeReduction.  C8 actualArithmeticDegree is the profile
degree of the C6 denominator-scaled lambda profile.

This file records the exact reduction of (Ob3-3) to a scalar identity between
the production degree donor and the actual C8 normalized log-volume, and the
single missing source identification.  No free Real parameter is introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8Closure.C8DegreeActual

namespace LeanFormal.IUT.N8Closure.C8DetDonorSearch

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {iota : Type v} [Fintype iota] {V : iota → Type w}
  {places : (i : iota) → V i → FinitePlaceAtPrime K p}
  {tuple : (i : iota) → V i}
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
  [Measure.IsAddHaarMeasure mu]

/-- The production degree donor is the finite sum of the realified profile. -/
theorem profileArithmeticDegree_eq_sum
    {Place : Type*} [Fintype Place] (profile : Place → ℝ) :
    profileArithmeticDegree profile =
      ∑ place, profile place :=
  rfl

/-- Exact (Ob3-3) target in the actual C8 data: production arithmetic degree of
the C6 lambda profile equals the actual C8 normalized log-volume of the C6 IQ
hull. -/
def C8Ob33SourceDonor
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (B : C6ActualIQData places tuple mu) : Prop :=
  actualArithmeticDegree C6 = B.normalizedLogVolume B.hull

/-- Exact reduction of (Ob3-3) to the scalar degree-sum identity through the
production donor. -/
theorem c8Ob33_iff_denominator_mul_sum_eq
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (B : C6ActualIQData places tuple mu) :
    C8Ob33SourceDonor C6 B ↔
      (C6.tupleWeights.denominator : ℝ) *
        (∑ i : iota, C6.lambdaData.lambda i) =
          B.normalizedLogVolume B.hull := by
  unfold C8Ob33SourceDonor
  rw [actualArithmeticDegree_eq_tupleDenominator_mul_sum]

end LeanFormal.IUT.N8Closure.C8DetDonorSearch
