import tmp.sheaf.xif.paper.S2176RamificationE1Actual
import tmp.sheaf.xif.paper.S2135Layer1SplitActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2187QVPlaceUnramifiedActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2176RamificationE1Actual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The qVFamily place unramified condition is exactly relative ramification
index one. -/
theorem s2187_unramified_iff_relativeRamificationIndex_one :
    S2040QVPlaceUnramifiedRequired T b ↔
      relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1 := by
  unfold S2040QVPlaceUnramifiedRequired
  rw [← localRamificationIndex_eq_relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b)]
/-- Exact missing arithmetic: the qVFamily place is unramified over Q. -/
def s2187QVFamUnramifiedRequired : Prop :=
  S2040QVPlaceUnramifiedRequired T b
/-- Exact missing global computation: the relative ramification index is one. -/
def s2187QVFamGlobalRamificationOne : Prop :=
  relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1
/-- Exact missing completion finrank condition (S2135) equivalent to degree one
plus unramified. -/
def s2187CompletionFinrankOne : Prop :=
  S2135CompletionFinrankOne (l := l) T b
/-- The root coefficient supply also needs the unchanged CommonPrimeCompletion
carrier bridge. -/
def s2187CompletionCarrierBridgeMissing : Prop :=
  s2176CompletionCarrierBridgeMissing (l := l) T b
#print axioms s2187_unramified_iff_relativeRamificationIndex_one
end LeanFormal.IUT.XiFPaper.S2187QVPlaceUnramifiedActual
end
