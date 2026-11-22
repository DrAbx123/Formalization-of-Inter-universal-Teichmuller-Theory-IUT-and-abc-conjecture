/- N5 link to the G1/P8 chain. -/
import tmp.sheaf.xif.paper.Mzk1G1P8ActualChainFinal
import tmp.sheaf.xif.paper.Mzk1G1P8CertificateActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8N5LinkFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8ActualChainFinal
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual

/-- Actual N5 condition and actual G1/P8 chain are available together. -/
theorem g1p8_n5_and_chain
    {A : ActualThm110Data}
    (C : G1P8ActualChain A)
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) ∧
      C.cover = g1ActualCover :=
  ⟨actual_n5_qSideSignedValueCondition T, rfl⟩

#check g1p8_n5_and_chain
end LeanFormal.IUT.XiFPaper.Mzk1G1P8N5LinkFinalActual
end
