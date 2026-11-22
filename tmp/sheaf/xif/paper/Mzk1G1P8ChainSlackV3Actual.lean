/- G1/P8 chain slack v3. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8ChainSlackV3Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
theorem g1p8ChainSlackV3 (A : ActualThm110Data) (S : G1P8DisplaySupply A) :
    S3171IUTIVSection1DisplayActual.thm110Lhs (g1p8DisplayTerms A) ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs (g1p8DisplayTerms A) :=
  thm110_display_of_hCor312 A (by
    simpa [g1p8DisplayTerms, S.terms_eq] using S.hCor312)
#check g1p8ChainSlackV3
end LeanFormal.IUT.XiFPaper.Mzk1G1P8ChainSlackV3Actual
end
