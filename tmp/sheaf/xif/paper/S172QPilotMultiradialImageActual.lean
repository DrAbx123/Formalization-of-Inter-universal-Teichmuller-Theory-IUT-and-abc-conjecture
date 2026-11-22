import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual
import tmp.sheaf.xif.paper.GenericQPilotCompletionPowerActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# S172: actual q-pilot multiradial image carrier/point/Haar

The multiradial image is constructed fiberwise over the actual bad places from
the source q-unit geometry:

  fiber b     = Block (sourceQGeometry T b),
  carrier     = product over b of the fibers,
  image point = product over b of genericQPilotImagePoint.

The per-b q-pilot lambda-O region is qParameterUnitLambdaHull, and the image is
the product of these hulls.  The actual product Haar is Measure.pi of the
per-fiber Haar data; the image Haar is its restriction to the image hull.  The
image mu_log is the Haar log-volume of that restricted measure.

The point lies in the hull under the actual qUnit norm <= 1 hypothesis.  The
remaining paper-object gap (Ind1/2/3 action compatibility and the identification
of this product hull with the paper multiradial image) is recorded exactly.
No inequality is asserted.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
variable (mu : ∀ b : Bad (nativePlaceSelection T),
  Measure (Block (G := sourceQGeometry (l := l) T b)))
variable [∀ b : Bad (nativePlaceSelection T),
  Measure.IsAddHaarMeasure (mu b)]

/-- The actual multiradial fiber at b. -/
abbrev QPilotMultiradialFiber
    (b : Bad (nativePlaceSelection T)) : Type :=
  Block (G := sourceQGeometry (l := l) T b)

/-- The actual multiradial carrier: product of the actual fibers. -/
abbrev QPilotMultiradialCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) -> QPilotMultiradialFiber (l := l) T b

/-- The actual multiradial image point from the qUnit data. -/
noncomputable def QPilotMultiradialImagePoint :
    QPilotMultiradialCarrier (l := l) T :=
  fun b => genericQPilotImagePoint
    (G := sourceQGeometry (l := l) T b)

/-- The actual per-fiber q-pilot lambda-O hull. -/
noncomputable def QPilotMultiradialFiberHull
    (b : Bad (nativePlaceSelection T)) :
    Set (QPilotMultiradialFiber (l := l) T b) :=
  qParameterUnitLambdaHull (G := sourceQGeometry (l := l) T b)

/-- The actual product image hull. -/
noncomputable def QPilotMultiradialImageHull :
    Set (QPilotMultiradialCarrier (l := l) T) :=
  Set.pi Set.univ (fun b =>
    QPilotMultiradialFiberHull (l := l) T b)

/-- The actual image point lies in the product image hull, under the actual
qUnit norm <= 1 hypothesis. -/
theorem QPilotMultiradialImagePoint_mem_hull
    (hq : ∀ b : Bad (nativePlaceSelection T),
      ‖(((sourceQGeometry (l := l) T b).qUnit PUnit.unit :
        CommonPrimeCompletion ((sourceQGeometry (l := l) T b).place PUnit.unit)))‖ ≤ 1) :
    QPilotMultiradialImagePoint (l := l) T ∈
      QPilotMultiradialImageHull (l := l) T := by
  intro b _
  exact genericQPilotImagePoint_mem_qUnitLambdaHull
    (G := sourceQGeometry (l := l) T b) (l := l)
    (fun _ => hq b)

/-- The actual product ambient Haar on the multiradial carrier. -/
noncomputable def QPilotMultiradialAmbientHaar :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  Measure.pi (fun b => mu b)

/-- The actual Haar transported to the image: restriction of the product Haar
to the product image hull. -/
noncomputable def QPilotMultiradialImageHaar :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  (QPilotMultiradialAmbientHaar (l := l) T mu).restrict
    (QPilotMultiradialImageHull (l := l) T)

/-- The actual image mu_log: Haar log-volume of the restricted image measure. -/
noncomputable def QPilotMultiradialImageMuLog : ENNReal :=
  haarLogVolume (QPilotMultiradialImageHaar (l := l) T mu)
    (QPilotMultiradialImageHull (l := l) T)

/-- Actual procession label factor as an ENNReal multiplier. -/
noncomputable def QPilotMultiradialProcessionFactor : ENNReal :=
  ENNReal.ofReal (productProcessionFactor (l := l))

/-- Procession-normalized image mu_log: the actual uniform label factor times
the actual image Haar log-volume. -/
noncomputable def QPilotMultiradialProcessionNormalizedMuLog : ENNReal :=
  QPilotMultiradialProcessionFactor (l := l) *
    QPilotMultiradialImageMuLog (l := l) T mu

/-- Actual multiradial image object over the fixed carrier. -/
structure QPilotMultiradialImageActual where
  imagePoint : QPilotMultiradialCarrier (l := l) T
  imagePoint_eq : imagePoint = QPilotMultiradialImagePoint (l := l) T
  imageHull : Set (QPilotMultiradialCarrier (l := l) T)
  imageHull_eq : imageHull = QPilotMultiradialImageHull (l := l) T
  ambientHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  ambientHaar_eq : ambientHaar = QPilotMultiradialAmbientHaar (l := l) T mu
  imageHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  imageHaar_eq : imageHaar = QPilotMultiradialImageHaar (l := l) T mu
  imageMuLog : ENNReal
  imageMuLog_eq : imageMuLog = QPilotMultiradialImageMuLog T mu
  processionFactor : ENNReal
  processionFactor_eq :
    processionFactor = QPilotMultiradialProcessionFactor (l := l)
  processionNormalizedMuLog : ENNReal
  processionNormalizedMuLog_eq :
    processionNormalizedMuLog =
      QPilotMultiradialProcessionNormalizedMuLog (l := l) T mu

/-- Actual multiradial image constructor. -/
noncomputable def qPilotMultiradialImageActual :
    QPilotMultiradialImageActual (l := l) T mu where
  imagePoint := QPilotMultiradialImagePoint (l := l) T
  imagePoint_eq := rfl
  imageHull := QPilotMultiradialImageHull (l := l) T
  imageHull_eq := rfl
  ambientHaar := QPilotMultiradialAmbientHaar (l := l) T mu
  ambientHaar_eq := rfl
  imageHaar := QPilotMultiradialImageHaar (l := l) T mu
  imageHaar_eq := rfl
  imageMuLog := QPilotMultiradialImageMuLog T mu
  imageMuLog_eq := rfl
  processionFactor := QPilotMultiradialProcessionFactor (l := l)
  processionFactor_eq := rfl
  processionNormalizedMuLog := QPilotMultiradialProcessionNormalizedMuLog (l := l) T mu
  processionNormalizedMuLog_eq := rfl

/-- Exact remaining paper-object gap: the Ind1/Ind2/Ind3 action compatibility
and the identification of the product qUnit hull with the paper multiradial
image are not supplied. -/
structure QPilotMultiradialPaperGap where
  ind1_action_compat : Prop
  ind2_action_compat : Prop
  ind3_action_compat : Prop
  image_hull_eq_paper : Prop
  image_haar_eq_paper : Prop

/-- The exact missing paper-object input. -/
def QPilotMultiradialPaperGapRequired : Prop :=
  Nonempty QPilotMultiradialPaperGap

end LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual

end
