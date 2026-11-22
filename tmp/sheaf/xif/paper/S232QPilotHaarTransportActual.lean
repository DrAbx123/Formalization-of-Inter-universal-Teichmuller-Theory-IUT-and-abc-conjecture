import tmp.sheaf.xif.paper.S191QPilotCarrierTransportActual
import tmp.sheaf.xif.paper.S178QPilotObjectFullActual
/-! # S232: qPilot carrier equivalence, Haar/mu_log transport, classical log
Uses the S191 carrier equivalence and image-point equality to connect the S156
qPilot classical object with the S172 multiradial image.  Constructs the
transported ambient Haar (Measure.map along s156ProductToBlock), the transported
image Haar (restriction to the multiradial image hull), the transported image
mu_log, and packages them with the classical qPilot log in one actual object.
No inequality. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S232QPilotHaarTransportActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- S156 qPilot image point equals the qVFamily product point. -/
theorem QPilotImagePoint_eq_dependentQVFamProductPoint :
    QPilotImagePoint T = dependentQVFamProductPoint T := rfl
/-- The carrier equivalence preserves the qPilot image: the S156 point maps
exactly to the S172 multiradial image point. -/
theorem s156ProductToBlock_QPilotImagePoint :
    s156ProductToBlock T (QPilotImagePoint T) =
      QPilotMultiradialImagePoint (l := l) T :=
  (QPilotMultiradialImagePoint_eq_s156ProductToBlock T).symm
/-- The transported ambient Haar from the S156 qPilot product. -/
noncomputable def qPilotTransportedAmbientHaar :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  Measure.map (s156ProductToBlock T) (QPilotAmbientHaar T)
/-- The transported image Haar: restriction to the S172 multiradial image hull. -/
noncomputable def qPilotTransportedImageHaar :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  (qPilotTransportedAmbientHaar T).restrict
    (QPilotMultiradialImageHull (l := l) T)
/-- The transported image mu_log. -/
noncomputable def qPilotTransportedImageMuLog : ENNReal :=
  haarLogVolume (qPilotTransportedImageHaar T)
    (QPilotMultiradialImageHull (l := l) T)
/-- Actual qPilot object connecting classical log, carrier image, transported
Haar and image mu_log. -/
structure QPilotHaarTransportActual where
  side : QPilotSideObjectActual T
  side_eq : side = qPilotSideObjectActual T
  imagePoint : QPilotMultiradialCarrier (l := l) T
  imagePoint_eq : imagePoint = QPilotMultiradialImagePoint (l := l) T
  imagePoint_is_qPilot : imagePoint = s156ProductToBlock T (QPilotImagePoint T)
  transportedAmbientHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  transportedAmbientHaar_eq : transportedAmbientHaar = qPilotTransportedAmbientHaar T
  transportedImageHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  transportedImageHaar_eq : transportedImageHaar = qPilotTransportedImageHaar T
  transportedImageMuLog : ENNReal
  transportedImageMuLog_eq : transportedImageMuLog = qPilotTransportedImageMuLog T
  classicalLog : Real
  classicalLog_eq : classicalLog = QPilotClassicalLog T
/-- Actual qPilot transport object inhabitant. -/
noncomputable def qPilotHaarTransportActual : QPilotHaarTransportActual T where
  side := qPilotSideObjectActual T
  side_eq := rfl
  imagePoint := QPilotMultiradialImagePoint (l := l) T
  imagePoint_eq := rfl
  imagePoint_is_qPilot := (s156ProductToBlock_QPilotImagePoint T).symm
  transportedAmbientHaar := qPilotTransportedAmbientHaar T
  transportedAmbientHaar_eq := rfl
  transportedImageHaar := qPilotTransportedImageHaar T
  transportedImageHaar_eq := rfl
  transportedImageMuLog := qPilotTransportedImageMuLog T
  transportedImageMuLog_eq := rfl
  classicalLog := QPilotClassicalLog T
  classicalLog_eq := rfl
/-- The classical log and the transported image mu_log live in the same actual
object. -/
theorem classicalLog_and_imageMuLog_same_object :
    (qPilotHaarTransportActual T).classicalLog = QPilotClassicalLog T ∧
      (qPilotHaarTransportActual T).transportedImageMuLog =
        qPilotTransportedImageMuLog T :=
  ⟨rfl, rfl⟩
end LeanFormal.IUT.XiFPaper.S232QPilotHaarTransportActual
