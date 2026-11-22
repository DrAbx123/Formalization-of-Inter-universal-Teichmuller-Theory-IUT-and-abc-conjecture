/- U-C support: actual weighted packet hull from U-L weights and the base StepV bound. -/
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import tmp.sheaf.xif.paper.Mzk1P6RootParameterWeightActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
open LeanFormal.IUT.XiFPaper.Mzk1P6RootParameterWeightActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6WeightedPacketHullActual
/-- The actual weighted packet-hull value from the StepV procession. -/
noncomputable def ULPacketHullValue
    (n : Nat) (D Q S T : Real) : Real :=
  (1 / (n : Real)) *
    (∑ j ∈ Finset.Icc 1 n,
      LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : Real) + 1) D Q S T j)
/-- The actual weighted packet-hull upper bound from the base StepV theorem. -/
noncomputable def ULPacketHullBound
    (n : Nat) (D Q S T : Real) : Real :=
  ((2 * (n : Real) + 1) + 1) / 4 *
    ((1 + 4 / (2 * (n : Real) + 1)) * D - Q / 6 +
      4 / (2 * (n : Real) + 1) * S + 20 / 3 * T)
/-- U-L actual weighted packet hull is bounded by the base StepV bound,
with no hCor312 and no assumption that the global theta hull log is zero. -/
theorem uL_weightedPacketHull_le
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ULPacketHullValue n D Q S T ≤ ULPacketHullBound n D Q S T :=
  p6_stepVAverages_ivInequality n hn D Q S T hD hS hT
/-- Actual weighted root-parameter sum entering the packet hull. -/
theorem uL_weightedPacketHull_root_sum
    {p : Nat} {K : Type*} [NormedField K] {ι : Type*} [Fintype ι]
    (X : LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.DistinguishedScalarData p K)
    (w : ι → Real) :
    (∑ i : ι, w i * LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.ord
        (K := K) p (LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual.theta X.alpha X.j)) =
      (∑ i : ι, w i) * rootParameterWeight X :=
  weighted_rootParameter_sum X w
#print axioms uL_weightedPacketHull_le
#print axioms uL_weightedPacketHull_root_sum
end LeanFormal.IUT.XiFPaper.Mzk1P6WeightedPacketHullActual
end
