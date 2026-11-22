import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

def sourcePointVolumeSigned (v : V) (x : I.ThetaPilotPoint v) : ENNReal :=
  ENNReal.ofReal (-I.sourceLocalLogDegree v x)

def sourceSetVolumeSigned (v : V) (S : Set (I.ThetaPilotPoint v)) : ENNReal :=
  ⨆ x ∈ S, sourcePointVolumeSigned I v x

theorem sourceSetVolumeSigned_mono (v : V) {S T : Set (I.ThetaPilotPoint v)}
    (hST : S <= T) :
    sourceSetVolumeSigned I v S <= sourceSetVolumeSigned I v T := by
  unfold sourceSetVolumeSigned
  refine iSup_le_iff.mpr ?_
  intro x
  refine iSup_le_iff.mpr ?_
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

#check sourcePointVolumeSigned
#check sourceSetVolumeSigned
#check sourceSetVolumeSigned_mono

end LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual
end