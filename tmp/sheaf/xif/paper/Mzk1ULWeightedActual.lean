/- U-L weighted actual: root weights and StepV weighted average. -/
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
namespace LeanFormal.IUT.XiFPaper.Mzk1ULWeightedActual
theorem uL_weighted_root_sum {p : Nat} {K : Type*} [NormedField K]
    {ι : Type*} [Fintype ι] (X : DistinguishedScalarData p K) (w : ι → Real) :
    (∑ i : ι, w i * ord (K := K) p (theta X.alpha X.j)) =
      (∑ i : ι, w i) * rootParameterWeight X :=
  weighted_rootParameter_sum X w
theorem uL_stepV_weighted_average
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.Icc 1 n,
          LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
            (2 * (n : Real) + 1) D Q S T j) ≤
      ((2 * (n : Real) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
          4 / (2 * (n : Real) + 1) * S + 20 / 3 * T) :=
  p6_stepVAverages_ivInequality n hn D Q S T hD hS hT
#print axioms uL_weighted_root_sum
#print axioms uL_stepV_weighted_average
end LeanFormal.IUT.XiFPaper.Mzk1ULWeightedActual
end
