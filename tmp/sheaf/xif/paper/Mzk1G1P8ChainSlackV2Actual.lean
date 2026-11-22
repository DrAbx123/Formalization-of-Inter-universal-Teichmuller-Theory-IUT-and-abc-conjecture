/- G1/P8 chain slack v2. -/
import tmp.sheaf.xif.paper.Mzk1G1P8ActualChainFinal
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8ActualChainFinal
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8ChainSlackV2Actual
theorem g1p8Chain_slackV2 (A : ActualThm110Data) (C : G1P8ActualChain A) :
    thm110Lhs C.terms ≤ thm110Rhs C.terms := by
  have h := thm110_display_of_hCor312 A C.hCor312
  simpa [C.terms_eq] using h
#check g1p8Chain_slackV2
end LeanFormal.IUT.XiFPaper.Mzk1G1P8ChainSlackV2Actual
