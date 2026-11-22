import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesWitnessShaActual

/-! # ABC two-estimates numeric evidence / intermediate lemmas -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesEvidenceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesWitnessShaActual

/-- Consumer: the two named estimates imply `ABCConjecture` (evidence alias). -/
theorem abc_from_estimates_evidence (E : ABCTwoEstimates) : ABCConjecture :=
  abc_of_twoEstimates E

/-- Consumer: the two named estimates imply the additive height bound. -/
theorem heightBound_from_estimates_evidence (E : ABCTwoEstimates) :
    ABCFormAdditiveHeightBound :=
  heightBound_of_twoEstimates E

/-- Numeric non-vacuity witness: zero log-volume satisfies the volume-estimate
slot with `D = 0` whenever weights are nonnegative. -/
theorem zero_volume_estimate_evidence
    (hweight : forall (a c : Nat), 0 ≤ arithmeticWeight (abcRationalPoint a c)) :
    forall δ : Real, 0 < δ ->
      exists D : Real,
        forall a b c : Nat, IsABCTriple a b c ->
          (0 : Real) ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) + 0 + D :=
  zero_volume_estimate hweight

/-- Partial data with zero volume are completable once any height estimate is
supplied; the volume slot is not the obstruction. -/
theorem partial_zero_volume_completable
    (P : ABCTwoEstimatesPartial) : ABCConjecture :=
  abc_of_partial_of_height P

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesEvidenceActual
