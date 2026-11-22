/- G1P8 display chain final v4: slack on the chain. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplayChainFinalV3
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplayChainFinalV4
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplayChainFinalV3
theorem g1p8ChainV4_slack (A : ActualThm110Data) (C : G1P8DisplayChainV3 A) :
    S3171IUTIVSection1DisplayActual.thm110Lhs C.terms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs C.terms := by
  have h := thm110_display_of_hCor312 A C.hCor312
  simpa [C.terms_eq] using h
#check g1p8ChainV4_slack
end LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplayChainFinalV4
end
