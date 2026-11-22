import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
noncomputable section
universe u v w
namespace LeanFormal.IUT.XiFPaper.Node09H1bTensorVolumeActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
/-- H1b actual tensor signed volume in relative Haar form: log μ(integral
log-tensor lattice) − log μ(canonical unit reference). -/
theorem h1b_signed_volume_eq_relativeHaarLog
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleLogTensorUnitLogVolume places tuple =
      Real.log (μ ((arithmeticTupleIntegralLogLattice places tuple :
          Set (ArithmeticTensorTupleBlock places tuple)))).toReal -
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
  arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog places tuple μ
#check h1b_signed_volume_eq_relativeHaarLog
end LeanFormal.IUT.XiFPaper.Node09H1bTensorVolumeActual
end