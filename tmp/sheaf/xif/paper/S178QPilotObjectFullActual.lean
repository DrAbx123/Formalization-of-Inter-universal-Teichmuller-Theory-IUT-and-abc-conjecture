import tmp.sheaf.xif.paper.S156QPilotSideObjectActual
import tmp.sheaf.xif.paper.S172QPilotMultiradialImageActual
/-! # S178: full qPilot object with multiradial image and transported Haar/mu_log
Combines the actual qPilot-side data of S156 (q_v family, classical
order*log p log, procession normalization) with the actual multiradial image
construction of S172 (carrier, image point, image hull, product Haar, restricted
image Haar, image mu_log).  The Haar family used for the image is the genuine
Haar family, not Dirac.  No inequality is stated. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry T b))]
/-- Genuine Haar on each multiradial fiber. -/
noncomputable def qPilotImageHaarFamily :
    ∀ b : Bad (nativePlaceSelection T),
      Measure (Block (G := sourceQGeometry T b)) :=
  fun _ => Measure.addHaar
/-- The actual multiradial image object with the genuine transported Haar. -/
noncomputable def qPilotImageObject :
    QPilotMultiradialImageActual (l := l) T (qPilotImageHaarFamily T) :=
  qPilotMultiradialImageActual (l := l) T (qPilotImageHaarFamily T)
/-- The image carrier. -/
abbrev QPilotImageCarrier : Type :=
  QPilotMultiradialCarrier (l := l) T
/-- The actual image point. -/
noncomputable def QPilotImagePointFull : QPilotImageCarrier (l := l) T :=
  (qPilotImageObject T).imagePoint
/-- The actual transported image Haar. -/
noncomputable def QPilotImageHaarFull :
    Measure (QPilotImageCarrier (l := l) T) :=
  (qPilotImageObject T).imageHaar
/-- The actual image mu_log. -/
noncomputable def QPilotImageMuLogFull : ENNReal :=
  (qPilotImageObject T).imageMuLog
/-- The image point is exactly the S172 qUnit image point. -/
theorem QPilotImagePointFull_eq :
    QPilotImagePointFull T =
      QPilotMultiradialImagePoint (l := l) T :=
  (qPilotImageObject T).imagePoint_eq
/-- The transported image Haar is exactly the restriction of the product Haar
to the image hull. -/
theorem QPilotImageHaarFull_eq :
    QPilotImageHaarFull T =
      QPilotMultiradialImageHaar (l := l) T (qPilotImageHaarFamily T) :=
  (qPilotImageObject T).imageHaar_eq
/-- The image mu_log is exactly the Haar log-volume of the image Haar. -/
theorem QPilotImageMuLogFull_eq :
    QPilotImageMuLogFull T =
      QPilotMultiradialImageMuLog (l := l) T (qPilotImageHaarFamily T) :=
  (qPilotImageObject T).imageMuLog_eq
/-- Full actual qPilot object: side data + multiradial image/Haar/mu_log. -/
structure QPilotObjectFullActual where
  side : QPilotSideObjectActual T
  side_eq : side = qPilotSideObjectActual T
  image : QPilotMultiradialImageActual (l := l) T (qPilotImageHaarFamily T)
  image_eq : image = qPilotImageObject T
/-- Actual full qPilot object inhabitant. -/
noncomputable def qPilotObjectFullActual : QPilotObjectFullActual T where
  side := qPilotSideObjectActual T
  side_eq := rfl
  image := qPilotImageObject T
  image_eq := rfl
/-- Classical qPilot log from the full object. -/
noncomputable def QPilotObjectFullClassicalLog : Real :=
  (qPilotObjectFullActual T).side.classicalLog
/-- Procession-normalized qPilot log from the full object. -/
noncomputable def QPilotObjectFullProcessionLog : Real :=
  (qPilotObjectFullActual T).side.processionNormalizedLog
end LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
