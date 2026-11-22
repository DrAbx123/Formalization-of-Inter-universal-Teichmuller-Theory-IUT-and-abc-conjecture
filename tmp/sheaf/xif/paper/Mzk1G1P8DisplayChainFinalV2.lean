/- G1/P8 display chain final v2. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplayChainFinalV2
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
structure G1P8DisplayChainV2 (A : ActualThm110Data) where
  cover : FermatCoverData ℂ
  terms : Thm110DisplayTerms
  terms_eq : terms = g1p8DisplayTerms A
  hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs terms ≤
    S3171IUTIVSection1DisplayActual.thm110Mid terms +
      S3171IUTIVSection1DisplayActual.thm110Cor312Gap terms
noncomputable def g1p8DisplayChainV2 (A : ActualThm110Data)
    (h : S3171IUTIVSection1DisplayActual.thm110Lhs (g1p8DisplayTerms A) ≤
      S3171IUTIVSection1DisplayActual.thm110Mid (g1p8DisplayTerms A) +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap (g1p8DisplayTerms A)) :
    G1P8DisplayChainV2 A :=
  { cover := g1ActualCover
    terms := g1p8DisplayTerms A
    terms_eq := rfl
    hCor312 := h }
#check G1P8DisplayChainV2
#check g1p8DisplayChainV2
end LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplayChainFinalV2
end
