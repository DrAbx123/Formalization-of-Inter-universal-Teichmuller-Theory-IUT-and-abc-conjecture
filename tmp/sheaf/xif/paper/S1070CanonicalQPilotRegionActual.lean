import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.QVPilotClassicalRootContainmentActual
/-! # S1070: canonical qPilot region/log (INTERMEDIATE)
The canonical qPilot coefficient is qVFamPureCoefficient = -logb_p ||qVFamily q||
(the qVFamily order coefficient), NOT the theta root order/(2l).  The region
is actual.  The normalized log formula needs the exact normalized-generator
supply (norm-instance gap); it is recorded as the exact minimum. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1070CanonicalQPilotRegionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
noncomputable def canonicalQPilotRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
    (qVFamPureCoefficient T b)
noncomputable def canonicalQPilotLog : Real :=
  -((∑ _ : qVFamTensorV, qVFamPureCoefficient T b ()) *
    Real.log (qVFamTensorP T b : Real))
/-- Actual normalized log under the exact supply. -/
theorem canonicalQPilotLog_eq_of_supply
    (S : NormalizedGeneratorSupply T b)
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
      qVFamTensorTuple mu (canonicalQPilotRegion (l := l) T b) =
      canonicalQPilotLog (l := l) T b := by
  unfold canonicalQPilotRegion canonicalQPilotLog thetaTensorScaledRegion
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (qVFamPureFractionalScalingData_of_supply (l := l) T b S)
structure CanonicalQPilotData
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] where
  region : Set (qVFamTensorBlock T b)
  region_eq : region = canonicalQPilotRegion (l := l) T b
  log : Real
  log_eq : log = canonicalQPilotLog (l := l) T b
  normalizedLog_eq :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
      qVFamTensorTuple mu region = log
noncomputable def canonicalQPilotData_of_supply
    (S : NormalizedGeneratorSupply T b)
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    CanonicalQPilotData (l := l) T b mu where
  region := canonicalQPilotRegion (l := l) T b
  region_eq := rfl
  log := canonicalQPilotLog (l := l) T b
  log_eq := rfl
  normalizedLog_eq := canonicalQPilotLog_eq_of_supply (l := l) T b S mu
/-- Exact intermediate bridge to the classical order coefficient. -/
def S1070PureCoeffEqualsOrder : Prop :=
  ∀ i : qVFamTensorV, qVFamPureCoefficient T b i =
    qPilotClassicalCoefficient T b i
def S1070Intermediate : Prop :=
  S1070PureCoeffEqualsOrder (l := l) T b ∧
    Nonempty (NormalizedGeneratorSupply (l := l) T b)
end LeanFormal.IUT.XiFPaper.S1070CanonicalQPilotRegionActual
