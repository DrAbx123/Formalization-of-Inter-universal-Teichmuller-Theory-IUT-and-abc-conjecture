/- P8 chain slack final. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ChainSlackFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
/-- The actual G1/P8 supplied display terms satisfy the Thm 1.10 slack. -/
theorem p8Chain_slack (A : ActualThm110Data) (S : G1P8DisplaySupply A) :
    thm110Lhs (g1p8DisplayTerms A) ≤ thm110Rhs (g1p8DisplayTerms A) :=
  thm110_display_of_hCor312 A (by
    simpa [g1p8DisplayTerms, S.terms_eq] using S.hCor312)
#check p8Chain_slack
end LeanFormal.IUT.XiFPaper.P8ChainSlackFinalActual
end
