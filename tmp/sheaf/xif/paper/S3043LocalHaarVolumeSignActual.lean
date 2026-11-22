import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual Haar log-volume is an `ENNReal.toReal`; hence nonnegative for
every measure value of the region. -/
theorem S3043_logVolume_nonneg :
    0 <= actualC3LogShellTensorLogVolume C3 :=
  ENNReal.toReal_nonneg

/-- Infinite Haar measure gives real log-volume 0. -/
theorem S3043_logVolume_eq_zero_of_infinite
    (h : actualC3LogShellTensorHaar C3 (actualC3LogShellTensorRegion C3) = ⊤) :
    actualC3LogShellTensorLogVolume C3 = 0 := by
  unfold actualC3LogShellTensorLogVolume haarLogVolume
  rw [if_pos h]
  simp

/-- Finite Haar measure at least 1 gives the logarithm of the measure. -/
theorem S3043_logVolume_eq_log_of_measure_ge_one
    (hfin : actualC3LogShellTensorHaar C3 (actualC3LogShellTensorRegion C3) < ⊤)
    (h1 : 1 <= actualC3LogShellTensorHaar C3 (actualC3LogShellTensorRegion C3)) :
    actualC3LogShellTensorLogVolume C3 =
      Real.log (actualC3LogShellTensorHaar C3
        (actualC3LogShellTensorRegion C3)).toReal :=
by
  have h1' : (1 : Real) <=
      (actualC3LogShellTensorHaar C3 (actualC3LogShellTensorRegion C3)).toReal :=
    (ENNReal.toReal_le_toReal ENNReal.one_ne_top hfin.ne).2 h1
  unfold actualC3LogShellTensorLogVolume haarLogVolume
  rw [if_neg hfin.ne, ENNReal.toReal_ofReal (Real.log_nonneg h1')]

#check S3043_logVolume_nonneg
#check S3043_logVolume_eq_zero_of_infinite
#check S3043_logVolume_eq_log_of_measure_ge_one
#print axioms S3043_logVolume_nonneg
#print axioms S3043_logVolume_eq_log_of_measure_ge_one

end LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
end
