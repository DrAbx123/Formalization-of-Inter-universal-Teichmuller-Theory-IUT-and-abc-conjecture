/- Actual G1/P8 chain: cover + display terms + hCor312 supply + N5. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1G1P8CertificateActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8ActualChainFinal

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual

/-- Actual G1/P8 chain data. -/
structure G1P8ActualChain (A : ActualThm110Data) where
  cover : FermatCoverData ℂ
  terms : Thm110DisplayTerms
  terms_eq : terms = g1p8DisplayTerms A
  hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs terms ≤ S3171IUTIVSection1DisplayActual.thm110Mid terms + S3171IUTIVSection1DisplayActual.thm110Cor312Gap terms

/-- Construct the actual G1/P8 chain from actual display terms and hCor312. -/
noncomputable def g1p8ActualChain (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs (g1p8DisplayTerms A) ≤
      S3171IUTIVSection1DisplayActual.thm110Mid (g1p8DisplayTerms A) + S3171IUTIVSection1DisplayActual.thm110Cor312Gap (g1p8DisplayTerms A)) :
    G1P8ActualChain A :=
  g1p8DisplaySupply A hCor312

/-- Actual N5 condition used by the chain. -/
theorem g1p8Chain_n5 {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  actual_n5_qSideSignedValueCondition T

#check G1P8ActualChain
#check g1p8ActualChain
#check g1p8Chain_n5

end LeanFormal.IUT.XiFPaper.Mzk1G1P8ActualChainFinal
end
