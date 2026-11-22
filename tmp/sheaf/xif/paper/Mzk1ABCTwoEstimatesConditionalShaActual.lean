import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesWitnessShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesEvidenceActual

/-! # ABC two-estimates conditional reduction (lattice Sha prefix) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesConditionalShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesWitnessShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesEvidenceActual

/-- Conditional reduction: two estimates -> ABC (Sha-level re-export). -/
theorem twoEstimates_sha_to_abc (E : ABCTwoEstimates) : ABCConjecture :=
  abc_from_estimates_evidence E

/-- Conditional reduction: two estimates -> additive height bound. -/
theorem twoEstimates_sha_to_height (E : ABCTwoEstimates) :
    ABCFormAdditiveHeightBound :=
  heightBound_from_estimates_evidence E

/-- Numeric witness: zero-volume model satisfies the volume-estimate slot. -/
theorem zero_volume_witness_sha
    (hweight : forall (a c : Nat), 0 ≤ arithmeticWeight (abcRationalPoint a c)) :
    forall δ : Real, 0 < δ ->
      exists D : Real,
        forall a b c : Nat, IsABCTriple a b c ->
          (0 : Real) ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) + 0 + D :=
  zero_volume_estimate_evidence hweight

#print axioms twoEstimates_sha_to_abc
#print axioms zero_volume_witness_sha

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesConditionalShaActual
