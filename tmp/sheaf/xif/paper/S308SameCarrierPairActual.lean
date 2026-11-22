import tmp.sheaf.xif.paper.S302ComparisonReadySourcePairActual
import tmp.sheaf.xif.paper.PaperRootLValuedTensorCarrierActual
import tmp.sheaf.xif.paper.RootHullMeasureActual

/-!
# S308: same-carrier Theta/qPilot pair

The qPilot multiradial image and its transported Haar are moved to the Theta
root/L carrier by the actual qVFamToRootL map.  Theta-side root hull is moved by
the same map.  The pair's two sides therefore live in one carrier type,
RootLProductCarrier.  Only objects and compatibility formulas are constructed;
no inequality is stated.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S308SameCarrierPairActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual
open LeanFormal.IUT.XiFPaper.S302ComparisonReadySourcePairActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
open LeanFormal.IUT.XiFPaper.S232QPilotHaarTransportActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry T b))]

/-- The common root/L carrier. -/
abbrev RootLProductCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) -> RootLValuedCarrier T b

noncomputable instance rootLProductMeasurableSpace :
    MeasurableSpace (RootLProductCarrier T) := ⊤

/-- Actual map from the qPilot multiradial carrier to the common root/L
carrier, fiberwise by qVFamToRootL. -/
noncomputable def qPilotToRootLCarrier :
    QPilotMultiradialCarrier T -> RootLProductCarrier T :=
  fun x b => qVFamToRootL T b
    (show qVFamTensorBlock T b from x b)

/-- qPilot image point in the common root/L carrier. -/
noncomputable def qPilotImagePointInThetaCarrier : RootLProductCarrier T :=
  qPilotToRootLCarrier T (QPilotMultiradialImagePoint T)

/-- qPilot image hull in the common root/L carrier. -/
noncomputable def qPilotImageHullInThetaCarrier : Set (RootLProductCarrier T) :=
  qPilotToRootLCarrier T '' QPilotMultiradialImageHull T

/-- Theta root hull in the same common root/L carrier. -/
noncomputable def thetaRootHullInThetaCarrier : Set (RootLProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    qVFamToRootL T b '' rootNormHull T b)

/-- Transferred qPilot image Haar in the common root/L carrier. -/
noncomputable def qPilotImageHaarInThetaCarrier :
    Measure (RootLProductCarrier T) :=
  Measure.map (qPilotToRootLCarrier T) (QPilotImageHaarFull T)

/-- Transferred qPilot image mu_log in the common root/L carrier. -/
noncomputable def qPilotImageMuLogInThetaCarrier : ENNReal :=
  haarLogVolume (qPilotImageHaarInThetaCarrier T)
    (qPilotImageHullInThetaCarrier T)

/-- Same-carrier comparison-ready pair. -/
structure SameCarrierSourcePair where
  theta : GlobalSourceThetaHullLogObject T
  theta_eq : theta = thetaSideOfPair T
  thetaHull : Set (RootLProductCarrier T)
  thetaHull_eq : thetaHull = thetaRootHullInThetaCarrier T
  qPilot : QPilotHaarTransportActual T
  qPilot_eq : qPilot = qPilotSideOfPair T
  qPilotImagePoint : RootLProductCarrier T
  qPilotImagePoint_eq : qPilotImagePoint = qPilotImagePointInThetaCarrier T
  qPilotImageHull : Set (RootLProductCarrier T)
  qPilotImageHull_eq : qPilotImageHull = qPilotImageHullInThetaCarrier T
  qPilotImageHaar : Measure (RootLProductCarrier T)
  qPilotImageHaar_eq : qPilotImageHaar = qPilotImageHaarInThetaCarrier T
  qPilotImageMuLog : ENNReal
  qPilotImageMuLog_eq : qPilotImageMuLog = qPilotImageMuLogInThetaCarrier (T := T)

/-- Actual same-carrier pair constructor. -/
noncomputable def sameCarrierSourcePair : SameCarrierSourcePair T where
  theta := thetaSideOfPair T
  theta_eq := rfl
  thetaHull := thetaRootHullInThetaCarrier T
  thetaHull_eq := rfl
  qPilot := qPilotSideOfPair T
  qPilot_eq := rfl
  qPilotImagePoint := qPilotImagePointInThetaCarrier T
  qPilotImagePoint_eq := rfl
  qPilotImageHull := qPilotImageHullInThetaCarrier T
  qPilotImageHull_eq := rfl
  qPilotImageHaar := qPilotImageHaarInThetaCarrier T
  qPilotImageHaar_eq := rfl
  qPilotImageMuLog := qPilotImageMuLogInThetaCarrier (T := T)
  qPilotImageMuLog_eq := rfl

/-- Both qPilot fields lie in the same root/L carrier as the Theta side by
construction. -/
theorem sameCarrierSourcePair_sameCarrier :
    (sameCarrierSourcePair T).qPilotImagePoint =
        qPilotToRootLCarrier T (QPilotMultiradialImagePoint T) ∧
      (sameCarrierSourcePair T).qPilotImageHull =
        qPilotToRootLCarrier T '' QPilotMultiradialImageHull T :=
  ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.S308SameCarrierPairActual

end
