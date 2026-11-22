import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

namespace LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- The actual normalized qPilot normalized log-volume, written directly as the
normalized volume of the fractional-lattice/holomorphic region at the actual
normalized coefficient. -/
noncomputable def qVFamNormalizedQPilotVolume : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    MeasureTheory.Measure.addHaar
    ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamNormalizedCoefficientFamily T b) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple) :
      Set (qVFamTensorBlock T b))

/-- Exact normalized-volume formula from the actual pure fractional scaling data. -/
theorem qVFamNormalizedQPilotVolume_eq :
    qVFamNormalizedQPilotVolume T b =
      -(qVFamNormalizedCoefficient T b) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold qVFamNormalizedQPilotVolume
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (p := qVFamTensorP T b) (places := qVFamTensorPlaces T b)
    (tuple := qVFamTensorTuple) (μ := MeasureTheory.Measure.addHaar)
    (qVFamNormalizedPureFractionalScalingData T b)]
  simp [qVFamNormalizedCoefficientFamily]

/-- The normalized qPilot volume is strictly negative. -/
theorem qVFamNormalizedQPilotVolume_neg :
    qVFamNormalizedQPilotVolume T b < 0 := by
  rw [qVFamNormalizedQPilotVolume_eq]
  have hc : 0 < qVFamNormalizedCoefficient T b :=
    qVFamNormalizedCoefficient_pos T b
  have hp : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (qVFamTensorP T b : Real) := Real.log_pos hp1
  nlinarith

/-- The actual unit-reference (label 0) normalized log-volume is zero. -/
theorem qVFamUnitRegionVolume_eq_zero :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
          Set (qVFamTensorBlock T b)) = 0 := by
  rw [coefficient_arithmeticTupleHolomorphicLattice (p := qVFamTensorP T b)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)]
  exact arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (μ := MeasureTheory.Measure.addHaar)

/-- Strict measure: the normalized qPilot region has strictly smaller
normalized log-volume than the label-0 unit region. -/
theorem qVFamNormalizedQPilotVolume_lt_unitRegion :
    qVFamNormalizedQPilotVolume T b <
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        MeasureTheory.Measure.addHaar
        (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
          Set (qVFamTensorBlock T b)) := by
  rw [qVFamUnitRegionVolume_eq_zero]
  exact qVFamNormalizedQPilotVolume_neg T b

/-- Correction form: the normalized volume is the paper-coefficient volume plus
the actual norm-ratio correction `log(qVFamNormRatio)`. -/
theorem qVFamNormalizedQPilotVolume_eq_paper_add_correction :
    qVFamNormalizedQPilotVolume T b =
      -(paperNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real)) +
        Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedQPilotVolume_eq]
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp0 : (0 : Real) < (qVFamTensorP T b : Real) := by exact_mod_cast hprime.pos
  have hpne1 : (qVFamTensorP T b : Real) ≠ 1 := by exact_mod_cast hprime.ne_one
  have hlog : Real.log (qVFamTensorP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp0 hpne1
  have hbridge := c_norm_eq_paperCoefficient_sub_normRatio (l := l) T b
  rw [hbridge]
  field_simp [hlog]
  ring

#print axioms qVFamNormalizedQPilotVolume_eq
#print axioms qVFamNormalizedQPilotVolume_lt_unitRegion
#print axioms qVFamNormalizedQPilotVolume_eq_paper_add_correction

def Node09P5NormalizedRegionStatus : List String :=
  [ "actual DONE: qVFamNormalizedQPilotVolume_eq = -qVFamNormalizedCoefficient * log p from actual qVFamNormalizedPureFractionalScalingData",
    "actual DONE: qVFamNormalizedQPilotVolume_lt_unitRegion gives strict measure of the normalized qPilot volume versus the label-0 unit region",
    "actual DONE: qVFamNormalizedQPilotVolume_eq_paper_add_correction carries the norm-ratio correction: volume = -paperCoefficient*log p + log(qVFamNormRatio)",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual