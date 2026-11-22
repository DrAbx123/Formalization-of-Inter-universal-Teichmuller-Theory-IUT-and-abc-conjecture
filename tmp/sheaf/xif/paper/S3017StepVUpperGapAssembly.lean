import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import tmp.sheaf.xif.paper.S3015FinalRealInequalityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S3015FinalRealInequalityActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3017StepVUpperGapAssembly

universe u v w

/-- PARTIAL S3017: average upper bound from S3014 procession data.
This is the average part only; the StepVUpper/assembly/CTheta pieces are
still missing (S3013/S3015/S3016). -/
theorem S3017_processionAverage_bound
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat)
    (D : S3014ProcessionData places tuple istar jValue exceptional l n) :
    (1 / (n : Real)) * (∑ label ∈ Icc 1 n, D.volume label) <=
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n :=
  S3014_processionAverage_of_data places tuple istar jValue exceptional l n D

/-- PARTIAL S3017: unfolded form of the average bound. -/
theorem S3017_processionAverage_bound_expanded
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat)
    (D : S3014ProcessionData places tuple istar jValue exceptional l n) :
    (1 / (n : Real)) * (∑ label ∈ Icc 1 n, D.volume label) <=
      (1 / (n : Real)) *
        ∑ label ∈ Icc 1 n,
          S3014PerLabelBound places tuple istar jValue exceptional l label := by
  simpa [S3014ProcessionAverageBound] using
    S3017_processionAverage_bound places tuple istar jValue exceptional l n D


/-- PARTIAL S3017: the CTheta upper from S3015, conditional on the exact
height-to-procession input. -/
theorem S3017_CTheta_upper_of_height
    (n : Nat) (hn : 2 <= n)
    (hheight : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcJInvariant a b c) <=
        (1 / (n : Real)) *
          ∑ j ∈ Icc 1 n,
            LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
              (2 * (n : Real) + 1) S2921D (S2921Q a b c)
              (S2921S a b c) (S2921T a b c) j)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) <=
      S3015FinalBound n a b c :=
  S3015_final_real_inequality n hn hheight a b c habc

#check S3017_CTheta_upper_of_height
#check S3017_processionAverage_bound
#check S3017_processionAverage_bound_expanded
#print axioms S3017_processionAverage_bound
#print axioms S3017_processionAverage_bound_expanded

end LeanFormal.IUT.XiFPaper.S3017StepVUpperGapAssembly
end
