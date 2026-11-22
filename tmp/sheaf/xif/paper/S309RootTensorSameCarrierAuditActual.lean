import tmp.sheaf.xif.paper.S308SameCarrierPairActual
import tmp.sheaf.xif.paper.S307QPilotThetaCarrierActual
import tmp.sheaf.xif.paper.PaperRootTensorThetaCarrierActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual

/-!
# S309: audit and rootTensorBlock same-carrier construction

S308 used RootLProductCarrier = product of (qVFam block tensor RootL).  That is
not the ThetaSideObject carrier rootTensorBlock.  This file:

* constructs the actual Theta rootTensorBlock product hull/Haar/mu_log directly;
* records the exact qPilot-to-rootTensorBlock base-change object, including its
  compatibility with qVFamToRootL;
* constructs a same-carrier pair only conditional on such an actual base change;
* records the exact dimension obstruction from S307.

No fake equivalence, no inequality.
-/

noncomputable section
open scoped BigOperators Pointwise TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S309RootTensorSameCarrierAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.QSideRootLValuedBridgeActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorThetaCarrierActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S301GlobalThetaHullLogActual
open LeanFormal.IUT.XiFPaper.S302ComparisonReadySourcePairActual
open LeanFormal.IUT.XiFPaper.S307QPilotThetaCarrierActual
open LeanFormal.IUT.XiFPaper.S308SameCarrierPairActual
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

/-- ThetaSideObject carrier, fiberwise. -/
abbrev ThetaRootTensorProductCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) -> rootTensorBlock T b

/-- Actual Theta root-tensor product hull. -/
noncomputable def thetaRootTensorProductHull :
    Set (ThetaRootTensorProductCarrier T) :=
  Set.pi Set.univ (fun b => rootTensorFieldUnitLambdaOHull T b)

/-- Actual Theta root-tensor product Haar. -/
noncomputable def thetaRootTensorProductHaar :
    Measure (ThetaRootTensorProductCarrier T) :=
  Measure.pi (fun b => rootTensorHaar T b)

/-- Actual Theta root-tensor product mu_log. -/
noncomputable def thetaRootTensorProductMuLog : ENNReal :=
  haarLogVolume (thetaRootTensorProductHaar T)
    (thetaRootTensorProductHull T)

/-- Exact qPilot-to-rootTensorBlock base-change object.  It is an actual family
of linear maps whose compatibility with qVFamToRootL is required. -/
structure QPilotRootTensorBaseChange where
  fiberMap : (b : Bad (nativePlaceSelection T)) ->
    qVFamTensorBlock T b →ₗ[ℚ_[qVFamTensorP T b]] rootTensorBlock T b
  compatible : ∀ (b : Bad (nativePlaceSelection T))
    (x : qVFamTensorBlock T b),
      qsideToRootLValued T b (fiberMap b x) = qVFamToRootL T b x

/-- Exact missing base-change object. -/
def QPilotRootTensorBaseChangeRequired : Prop :=
  Nonempty (QPilotRootTensorBaseChange T)

/-- qPilot image point in rootTensorBlock, conditional on an actual base change. -/
noncomputable def qPilotRootTensorImagePoint
    (M : QPilotRootTensorBaseChange T) : ThetaRootTensorProductCarrier T :=
  fun b => M.fiberMap b (qPilotBlockPoint T b)

/-- qPilot image hull in rootTensorBlock, conditional on an actual base change. -/
noncomputable def qPilotRootTensorImageHull
    (M : QPilotRootTensorBaseChange T) :
    Set (ThetaRootTensorProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    M.fiberMap b '' ({qPilotBlockPoint T b} : Set (qVFamTensorBlock T b)))

/-- Transferred qPilot Haar in rootTensorBlock, conditional on an actual base
change. -/
noncomputable def qPilotRootTensorHaar
    (M : QPilotRootTensorBaseChange T) :
    Measure (ThetaRootTensorProductCarrier T) :=
  Measure.map
    (fun x : QPilotMultiradialCarrier T => fun b => M.fiberMap b
      (show qVFamTensorBlock T b from x b))
    (QPilotImageHaarFull T)

/-- Transferred qPilot mu_log in rootTensorBlock, conditional on an actual base
change. -/
noncomputable def qPilotRootTensorMuLog
    (M : QPilotRootTensorBaseChange T) : ENNReal :=
  haarLogVolume (qPilotRootTensorHaar T M)
    (qPilotRootTensorImageHull T M)

/-- RootTensorBlock same-carrier pair, conditional on the actual base change. -/
structure RootTensorSameCarrierPair (M : QPilotRootTensorBaseChange T) where
  baseChange : QPilotRootTensorBaseChange T
  baseChange_eq : baseChange = M
  theta : GlobalSourceThetaHullLogObject T
  theta_eq : theta = thetaSideOfPair T
  thetaHull : Set (ThetaRootTensorProductCarrier T)
  thetaHull_eq : thetaHull = thetaRootTensorProductHull T
  thetaHaar : Measure (ThetaRootTensorProductCarrier T)
  thetaHaar_eq : thetaHaar = thetaRootTensorProductHaar T
  thetaMuLog : ENNReal
  thetaMuLog_eq : thetaMuLog = thetaRootTensorProductMuLog T
  qPilot : QPilotHaarTransportActual T
  qPilot_eq : qPilot = qPilotSideOfPair T
  qPilotImagePoint : ThetaRootTensorProductCarrier T
  qPilotImagePoint_eq : qPilotImagePoint = qPilotRootTensorImagePoint T M
  qPilotImageHull : Set (ThetaRootTensorProductCarrier T)
  qPilotImageHull_eq : qPilotImageHull = qPilotRootTensorImageHull T M
  qPilotHaar : Measure (ThetaRootTensorProductCarrier T)
  qPilotHaar_eq : qPilotHaar = qPilotRootTensorHaar T M
  qPilotMuLog : ENNReal
  qPilotMuLog_eq : qPilotMuLog = qPilotRootTensorMuLog T M

/-- Conditional actual rootTensorBlock pair constructor. -/
noncomputable def rootTensorSameCarrierPair
    (M : QPilotRootTensorBaseChange T) :
    RootTensorSameCarrierPair T M where
  baseChange := M
  baseChange_eq := rfl
  theta := thetaSideOfPair T
  theta_eq := rfl
  thetaHull := thetaRootTensorProductHull T
  thetaHull_eq := rfl
  thetaHaar := thetaRootTensorProductHaar T
  thetaHaar_eq := rfl
  thetaMuLog := thetaRootTensorProductMuLog T
  thetaMuLog_eq := rfl
  qPilot := qPilotSideOfPair T
  qPilot_eq := rfl
  qPilotImagePoint := qPilotRootTensorImagePoint T M
  qPilotImagePoint_eq := rfl
  qPilotImageHull := qPilotRootTensorImageHull T M
  qPilotImageHull_eq := rfl
  qPilotHaar := qPilotRootTensorHaar T M
  qPilotHaar_eq := rfl
  qPilotMuLog := qPilotRootTensorMuLog T M
  qPilotMuLog_eq := rfl

/-- The exact missing input for an actual same-rootTensor pair. -/
theorem rootTensorPair_iff_baseChange :
    Nonempty (Sigma (fun M : QPilotRootTensorBaseChange T =>
      RootTensorSameCarrierPair T M)) ↔
      QPilotRootTensorBaseChangeRequired T := by
  constructor
  · rintro ⟨⟨M, P⟩⟩
    exact ⟨P.baseChange⟩
  · rintro ⟨M⟩
    exact ⟨⟨M, rootTensorSameCarrierPair T M⟩⟩

end LeanFormal.IUT.XiFPaper.S309RootTensorSameCarrierAuditActual

end
