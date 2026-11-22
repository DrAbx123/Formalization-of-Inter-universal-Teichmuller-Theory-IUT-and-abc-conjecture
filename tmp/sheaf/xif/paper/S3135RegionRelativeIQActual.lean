import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135RegionRelativeIQActual

/-- **A26 (c) shape at the concrete IQ carrier** (`RegionRelativeToHullAndWeight`):
hull volume bounded by `ofReal theta`, hull volume finite, and the weight bounded by
`theta`. -/
def S3135RegionRelativeToHullAndWeightW
    {X : Type} (W : IQHullLogVolumeInterface X) (weight theta : ℝ) : Prop :=
  W.logVolume W.hull ≤ ENNReal.ofReal theta ∧
    W.logVolume W.hull < ⊤ ∧ weight ≤ theta

/-- **Instantiation at the concrete IQ carrier**: the tree's
`iqCarrierModelInterface` (prior art IQCarrierConcreteModel.lean:193; concrete
hweightvol/hpoint/lunit at :346/:358/:386) with the tree's Card-AMPL theta-bound supply
(CardAMPLThetaBoundSupply.lean:78-84) satisfies the (c) shape as soon as the weight is
bounded by the supply constant `S.theta`.  The hull-volume inequality and its
finiteness are DISCHARGED from the supply; the EXACT REMAINING HYPOTHESIS is
`weight ≤ S.theta` (the IV section 2 normalization/weight input, not derivable from
R1). -/
theorem s3135_regionRelative_iqCarrier
    (weight : ℝ) (S : CardAMPLThetaBoundSupply (iqCarrierModelInterface))
    (hweight : weight ≤ S.theta) :
    S3135RegionRelativeToHullAndWeightW iqCarrierModelInterface weight S.theta := by
  refine ⟨S.hull_logVolume_le, ?_, hweight⟩
  exact lt_of_le_of_lt S.hull_logVolume_le ENNReal.ofReal_lt_top

#check S3135RegionRelativeToHullAndWeightW
#check s3135_regionRelative_iqCarrier
end LeanFormal.IUT.XiFPaper.S3135RegionRelativeIQActual
end
