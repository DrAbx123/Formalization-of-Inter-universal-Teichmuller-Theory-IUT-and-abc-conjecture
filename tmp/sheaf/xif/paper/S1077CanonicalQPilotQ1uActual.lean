import tmp.sheaf.xif.paper.S1070CanonicalQPilotRegionActual
/-! # S1077: canonical qPilot q[1u] region/log
Uses the qVFamPureCoefficient (qVFamily order coefficient), never the theta
root cRoot=order/(2l) and never a supplied c_norm.  The region is actual; the
normalized log formula is actual under the exact normalized-generator supply.
INTERMEDIATE until theta root stack. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1077CanonicalQPilotQ1uActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.S1070CanonicalQPilotRegionActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- Canonical qPilot q[1u] region: F(qVFamPureCoefficient) * O_hol. -/
abbrev qPilotQ1uRegion (b : Bad (nativePlaceSelection T)) :
    Set (qVFamTensorBlock T b) :=
  canonicalQPilotRegion (l := l) T b
/-- Canonical qPilot q[1u] log formula. -/
abbrev qPilotQ1uLog (b : Bad (nativePlaceSelection T)) : Real :=
  canonicalQPilotLog (l := l) T b
/-- Exact normalized-generator supply; the only missing norm-instance bridge
between Completion and CommonPrimeCompletion. -/
abbrev S1077NormalizedSupply (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (NormalizedGeneratorSupply (l := l) T b)
/-- Actual normalized log formula from the exact supply. -/
theorem qPilotQ1uLog_eq_of_supply
    (S : NormalizedGeneratorSupply (l := l) T b)
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
      qVFamTensorTuple mu (qPilotQ1uRegion T b) =
      qPilotQ1uLog T b :=
  canonicalQPilotLog_eq_of_supply (l := l) T b S mu
/-- Exact positivity/finiteness package for the canonical region. -/
structure S1077RegionData
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] where
  region_pos : 0 < mu (qPilotQ1uRegion (l := l) T b)
  region_finite : mu (qPilotQ1uRegion (l := l) T b) < ⊤
  log_eq : arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (qPilotQ1uRegion (l := l) T b) = qPilotQ1uLog (l := l) T b
end LeanFormal.IUT.XiFPaper.S1077CanonicalQPilotQ1uActual
