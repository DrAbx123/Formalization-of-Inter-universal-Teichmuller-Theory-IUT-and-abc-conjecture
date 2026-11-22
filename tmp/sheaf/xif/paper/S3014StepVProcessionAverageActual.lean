import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVLambda

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual

universe u v w

noncomputable def S3014PerLabelBound
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l label : Nat) : Real :=
  (-(stepVLambda p label jValue l) +
      ((∑ i, localNormOrder p
        (arithmeticTupleLocalDifferent places tuple i)) + 1)) * Real.log (p : Real) +
    ∑ i ∈ exceptional,
      (3 + Real.log
        (logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real))

noncomputable def S3014ProcessionAverageBound
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l : Nat) (n : Nat) : Real :=
  (1 / (n : Real)) *
    ∑ label ∈ Icc 1 n,
      S3014PerLabelBound places tuple istar jValue exceptional l label

/-- Procession-normalized average of a per-label volume family is bounded by
the average of the per-label Step (v) bounds. -/
theorem S3014_processionAverage_le
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat)
    (volume : Nat -> Real)
    (h : forall label, label ∈ Icc 1 n ->
      volume label <=
        S3014PerLabelBound places tuple istar jValue exceptional l label) :
    (1 / (n : Real)) * (∑ label ∈ Icc 1 n, volume label) <=
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n := by
  unfold S3014ProcessionAverageBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum (fun label hlabel => h label hlabel)

/-- Exact missing family: per-label existential representatives are not a
uniform function of the label.  A choice family plus its per-label bound is
the explicit input needed to instantiate `volume`. -/
structure S3014ProcessionData
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat) where
  volume : Nat -> Real
  perLabel_bound :
    forall label, label ∈ Icc 1 n ->
      volume label <=
        S3014PerLabelBound places tuple istar jValue exceptional l label

theorem S3014_processionAverage_of_data
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat)
    (D : S3014ProcessionData places tuple istar jValue exceptional l n) :
    (1 / (n : Real)) * (∑ label ∈ Icc 1 n, D.volume label) <=
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  S3014_processionAverage_le places tuple istar jValue exceptional l n
    D.volume D.perLabel_bound

#check S3014PerLabelBound
#check S3014ProcessionAverageBound
#check S3014_processionAverage_le
#check S3014ProcessionData
#check S3014_processionAverage_of_data
#print axioms S3014_processionAverage_le
#print axioms S3014_processionAverage_of_data

end LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
end