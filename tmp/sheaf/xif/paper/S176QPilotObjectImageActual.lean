import tmp.sheaf.xif.paper.S172QPilotMultiradialImageActual
import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
/-! # S176: actual qPilot object with multiradial image and transported Haar/mu_log
The q-pilot object is built from the actual local q_v = qVFamily, its zero-locus
divisor, the actual multiradial image carrier/point/hull of S172, the actual
product Haar and restricted image Haar, the image mu_log, the classical
order*log(residueNormBase) q log, and the actual F_l^x procession average.
No inequality and no correction target is stated. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S176QPilotObjectImageActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- The actual Haar family: genuine Haar on every multiradial fiber. -/
noncomputable def qPilotMultiradialActualHaarFamily :
    ∀ b : Bad (nativePlaceSelection T),
      Measure (Block (G := sourceQGeometry (l := l) T b)) :=
  fun _ => Measure.addHaar
/-- The actual product Haar on the multiradial carrier. -/
noncomputable def qPilotMultiradialAmbientHaarActual :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  QPilotMultiradialAmbientHaar (l := l) T
    (qPilotMultiradialActualHaarFamily T)
/-- The transported image Haar: actual product Haar restricted to the hull. -/
noncomputable def qPilotMultiradialImageHaarActual :
    Measure (QPilotMultiradialCarrier (l := l) T) :=
  QPilotMultiradialImageHaar (l := l) T
    (qPilotMultiradialActualHaarFamily T)
/-- The actual image mu_log from the transported Haar. -/
noncomputable def qPilotMultiradialImageMuLogActual : ENNReal :=
  QPilotMultiradialImageMuLog (l := l) T
    (qPilotMultiradialActualHaarFamily T)
/-- The actual multiradial qPilot image object. -/
structure QPilotMultiradialImageHaarActual where
  imagePoint : QPilotMultiradialCarrier (l := l) T
  imagePoint_eq : imagePoint = QPilotMultiradialImagePoint (l := l) T
  imageHull : Set (QPilotMultiradialCarrier (l := l) T)
  imageHull_eq : imageHull = QPilotMultiradialImageHull (l := l) T
  ambientHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  ambientHaar_eq : ambientHaar = qPilotMultiradialAmbientHaarActual T
  imageHaar : Measure (QPilotMultiradialCarrier (l := l) T)
  imageHaar_eq : imageHaar = qPilotMultiradialImageHaarActual T
  imageMuLog : ENNReal
  imageMuLog_eq : imageMuLog = qPilotMultiradialImageMuLogActual T
/-- Actual inhabitant of the multiradial qPilot image. -/
noncomputable def qPilotMultiradialImageHaarActual :
    QPilotMultiradialImageHaarActual T where
  imagePoint := QPilotMultiradialImagePoint (l := l) T
  imagePoint_eq := rfl
  imageHull := QPilotMultiradialImageHull (l := l) T
  imageHull_eq := rfl
  ambientHaar := qPilotMultiradialAmbientHaarActual T
  ambientHaar_eq := rfl
  imageHaar := qPilotMultiradialImageHaarActual T
  imageHaar_eq := rfl
  imageMuLog := qPilotMultiradialImageMuLogActual T
  imageMuLog_eq := rfl
/-- Classical paper q-pilot log: ord_v(q_v)*log(residueNormBase). -/
noncomputable def qPilotClassicalLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) *
        Real.log (residueNormBase (qVFamTensorPlace T b)))
/-- Actual F_l^x procession normalization of the qPilot log. -/
noncomputable def qPilotProcessionNormalizedLog : Real :=
  processionAverage l (fun _ : ProcessionLabel l => qPilotClassicalLog T)
/-- The procession average of the constant qPilot label function equals the
classical qPilot log. -/
theorem qPilotProcessionNormalizedLog_eq :
    qPilotProcessionNormalizedLog T = qPilotClassicalLog T := by
  unfold qPilotProcessionNormalizedLog qPilotClassicalLog processionAverage
    processionLabelWeight
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (ProcessionLabel l) : Real) ≠ 0 :=
    by exact_mod_cast Fintype.card_ne_zero (α := ProcessionLabel l)
  field_simp [hcard]
/-- Actual qPilot object: q_v family, divisor, multiradial image with Haar/mu_log,
classical log, procession normalization. -/
structure QPilotObjectActual where
  qParameter : (b : Bad (nativePlaceSelection T)) →
    FinitePlaceQCandidate ((nativeBadLift T).lift b)
  qParameter_eq : qParameter = qVFamily T
  localDivisor : (b : Bad (nativePlaceSelection T)) →
    IUTIVArithmeticDivisor T.arithmetic.F
  localDivisor_eq : localDivisor = qVZeroLocusLocalDivisor T
  globalDivisor : IUTIVArithmeticDivisor T.arithmetic.F
  globalDivisor_eq : globalDivisor = qVZeroLocusGlobalDivisor T
  image : QPilotMultiradialImageHaarActual T
  classicalLog : Real
  classicalLog_eq : classicalLog = qPilotClassicalLog T
  processionLog : Real
  processionLog_eq : processionLog = qPilotProcessionNormalizedLog T
/-- Actual qPilot object inhabitant. -/
noncomputable def qPilotObjectActual : QPilotObjectActual T where
  qParameter := qVFamily T
  qParameter_eq := rfl
  localDivisor := qVZeroLocusLocalDivisor T
  localDivisor_eq := rfl
  globalDivisor := qVZeroLocusGlobalDivisor T
  globalDivisor_eq := rfl
  image := qPilotMultiradialImageHaarActual T
  classicalLog := qPilotClassicalLog T
  classicalLog_eq := rfl
  processionLog := qPilotProcessionNormalizedLog T
  processionLog_eq := rfl
end LeanFormal.IUT.XiFPaper.S176QPilotObjectImageActual
