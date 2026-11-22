import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry
import tmp.sheaf.n8.closure.PaperP6ComparisonActual
import tmp.sheaf.n8.closure.PaperP6Final
import tmp.sheaf.n8.closure.C6UnitRefNormalized

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperValuesBoundedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.PaperP6Final
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block : Type := ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Any source output region contained in the C6 Theta hull has normalized
log-volume bounded by the Theta log-volume. -/
theorem paperValueLog_le_theta_of_subset
    (T : Set (Block S))
    (hT : T ⊆ c6Hull (places := places S) (tuple := tuple S)
      (rawData (places S) (tuple S))) :
    Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
      thetaLogVolume S := by
  have htheta_eq : thetaLogVolume S =
      Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
        (c6Hull (places := places S) (tuple := tuple S)
          (rawData (places S) (tuple S)))).toReal) := rfl
  by_cases hzero : c6UnitRefNormalizedData (places S) (tuple S) T = 0
  · rw [hzero, ENNReal.toReal_zero, Real.log_zero]
    exact thetaLogVolume_nonneg S
  by_cases htop : c6UnitRefNormalizedData (places S) (tuple S) T = ⊤
  · rw [htop, ENNReal.toReal_top, Real.log_zero]
    exact thetaLogVolume_nonneg S
  · have hle : c6UnitRefNormalizedData (places S) (tuple S) T ≤
        c6UnitRefNormalizedData (places S) (tuple S)
          (c6Hull (places := places S) (tuple := tuple S)
            (rawData (places S) (tuple S))) := by
      apply measure_mono hT
    have hSpos : 0 < (c6UnitRefNormalizedData (places S) (tuple S) T).toReal :=
      ENNReal.toReal_pos hzero htop
    have hHne : c6UnitRefNormalizedData (places S) (tuple S)
        (c6Hull (places := places S) (tuple := tuple S)
          (rawData (places S) (tuple S))) ≠ ⊤ :=
      ne_of_lt (thetaMass_lt_top S)
    have hHpos : 0 < (c6UnitRefNormalizedData (places S) (tuple S)
        (c6Hull (places := places S) (tuple := tuple S)
          (rawData (places S) (tuple S)))).toReal := by
      apply ENNReal.toReal_pos
      · intro hzeroH
        have hge := hull_mass_ge_one S
        rw [hzeroH] at hge
        exact zero_lt_one.not_ge hge
      · exact hHne
    have hreal : (c6UnitRefNormalizedData (places S) (tuple S) T).toReal ≤
        (c6UnitRefNormalizedData (places S) (tuple S)
          (c6Hull (places := places S) (tuple := tuple S)
            (rawData (places S) (tuple S)))).toReal :=
      ENNReal.toReal_mono hHne hle
    have hlog := Real.log_le_log hSpos hreal
    rw [htheta_eq]
    exact hlog

end LeanFormal.IUT.N8Closure.PaperValuesBoundedActual

end
