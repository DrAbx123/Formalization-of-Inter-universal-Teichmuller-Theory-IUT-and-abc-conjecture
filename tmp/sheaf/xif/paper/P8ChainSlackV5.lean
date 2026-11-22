/- P8 chain slack v5. -/
import tmp.sheaf.xif.paper.P8ChainSlackFinalActual
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ChainSlackV5
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.P8ChainSlackFinalActual
theorem p8ChainSlackV5 (A : ActualThm110Data) (S : G1P8DisplaySupply A) :
    S3171IUTIVSection1DisplayActual.thm110Lhs (g1p8DisplayTerms A) ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs (g1p8DisplayTerms A) :=
  p8Chain_slack A S
#check p8ChainSlackV5
end LeanFormal.IUT.XiFPaper.P8ChainSlackV5
end
