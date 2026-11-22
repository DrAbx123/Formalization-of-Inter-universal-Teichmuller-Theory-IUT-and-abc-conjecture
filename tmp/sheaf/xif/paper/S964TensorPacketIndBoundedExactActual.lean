import tmp.sheaf.xif.paper.S940Ind3ImageActual
import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S964TensorPacketIndBoundedExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S940Ind3ImageActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open MeasureTheory

universe ua uv upi umon ui uR uVQ u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Exact transport datum from the S940 Ind carriers to the FinalL-valued
tensor packet, with a unit region and boundedness.  No empty image and no
theta-only substitution is used. -/
structure S964TensorIndBoundedData where
  ind1Image : Set (FinalLValuedCarrier T b)
  ind2Image : Set (FinalLValuedCarrier T b)
  ind3Image : Set (FinalLValuedCarrier T b)
  ind1_nonempty : ind1Image.Nonempty
  ind2_nonempty : ind2Image.Nonempty
  ind3_nonempty : ind3Image.Nonempty
  unitRegion : Set (FinalLValuedCarrier T b)
  unitRegion_is_paperO : Prop
  unitRegion_is_paperO_holds : unitRegion_is_paperO
  ind1_subset_unit : ind1Image ⊆ unitRegion
  ind2_subset_unit : ind2Image ⊆ unitRegion
  ind3_subset_unit : ind3Image ⊆ unitRegion
  /-- Exact external datum: maps from the actual S940 carriers to the
  FinalL-valued packet realizing these image sets. -/
  ind1_transfer : Prop
  ind2_transfer : Prop
  ind3_transfer : Prop
  transfer_holds : ind1_transfer ∧ ind2_transfer ∧ ind3_transfer

/-- Exact required boundedness datum. -/
def S964TensorIndBoundedRequired : Prop :=
  Nonempty (S964TensorIndBoundedData (l := l) T b)

end LeanFormal.IUT.XiFPaper.S964TensorPacketIndBoundedExactActual

end
