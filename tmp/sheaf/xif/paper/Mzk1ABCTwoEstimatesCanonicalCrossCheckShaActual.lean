import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesReductionInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesNumericEvidenceActual

/-! # ABC two-estimates canonical cross-check (lattice Sha prefix) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesCanonicalCrossCheckShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionInterfaceActual

/-- Our Sha-level two estimates route matches the canonical interface (ABC). -/
theorem sha_abc_via_canonical (E : ABCTwoEstimates) : ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionInterfaceActual.two_estimates_to_abc E

/-- Our Sha-level route matches the canonical height-bound interface. -/
theorem sha_height_via_canonical (E : ABCTwoEstimates) :
    ABCFormAdditiveHeightBound :=
  LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionInterfaceActual.two_estimates_to_heightBound E

#print axioms sha_abc_via_canonical
#print axioms sha_height_via_canonical

end LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesCanonicalCrossCheckShaActual
