import tmp.sheaf.xif.paper.Mzk1BoxPrincipalScalarActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
/-! Alignment note between the principal-region scalar readout and the StepV packet readout.

The principal readout is `log(rootHaarFactor)/principalDim` and, by the green theorem
`principal_region_normalized_scalar`, equals `log ||lam||`.  The StepV packet readout is
`signedLocalReadout mu S O dim`.  No type-level equality between the root extension and the
actual tensor block is asserted; the comparison is recorded as an explicit bridge. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxPrincipalPacketAlignmentActual
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxPrincipalScalarActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
universe u v w
variable {l : PrimeGeFive}
/-- Principal-region scalar readout (`log mass / dim`). -/
noncomputable def principalScalarReadout
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (lam : (rootNormedExtension T b)ˣ) : Real :=
  Real.log ((rootHaarFactor T b lam).toReal) / (principalDim T b : Real)
/-- The principal readout is the signed log norm. -/
theorem principalScalarReadout_eq_log_norm
    (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
    (hd : principalDim T b ≠ 0) (lam : (rootNormedExtension T b)ˣ) :
    principalScalarReadout T b lam = Real.log ‖((lam : (rootNormedExtension T b)))‖ :=
  principal_region_normalized_scalar T b hd lam
/-- Explicit bridge: a principal-region value and a StepV packet readout value. -/
structure PacketScalarAlignment where
  value : Real
  principal_value : Real
  packet_value : Real
  principal_eq : value = principal_value
  packet_eq : value = packet_value
/-- Exact missing datum: identifying the principal-region value with the StepV packet scalar. -/
def principalPacketAlignmentMissing : List String :=
  [ "principal region lam * O in rootNormedExtension maps to the StepV distinguished slot",
    "rootHaarFactor value equals the normalized log ratio of the packet hull region" ]
theorem principalPacketAlignmentMissing_length :
    principalPacketAlignmentMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BoxPrincipalPacketAlignmentActual
end
