import tmp.sheaf.xif.paper.S2475S1473ValueLayerActual
import tmp.sheaf.xif.paper.S2456PaperFamilyActual

/-! # S2480: value-layer to ActualOutput map — exact missing fields

No actual map from `I.ThetaPilotPoint v` to `ActualOutput R` compatible with
the profile readout exists.  This file records the exact missing fields and
proves that a constant map forces the missing profile=qPilot identity.  The
value layer is not used as the paper family. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput
open LeanFormal.IUT.XiFPaper.S1447MarkedTraceActual
open LeanFormal.IUT.XiFPaper.S1473C9MarkedMapActual
open LeanFormal.IUT.XiFPaper.S2475S1473ValueLayerActual

universe ua uv upi umon ui u v ux

namespace LeanFormal.IUT.XiFPaper.S2480ValueLayerToActualOutputRequired

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (R3 : LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge.SourceTheorem311Realization l Label Choice)

/-- Exact missing map and readout compatibility. -/
structure S2480ValueLayerToActualOutputRequired where
  toOutput : I.ThetaPilotPoint v → ActualOutput R3
  profile_readout_compat : ∀ x,
    R3.input.profile.logVolume (toOutput x).source = readout I v x


theorem s2480_profile_eq_sourceQPilot_of_map
    (M : S2480ValueLayerToActualOutputRequired I v R3) :
    R3.input.profile.logVolume
        (M.toOutput (qMark I v R n)).source =
      I.sourceQPilotLogVolume v R n := by
  rw [M.profile_readout_compat (qMark I v R n), readout_qMark]

/-- A constant map to an output O is compatible only if the profile value of O
is the qPilot source value. -/
theorem s2480_constant_map_compat_forces_S2404
    (O : ActualOutput R3)
    (h : ∀ x, R3.input.profile.logVolume O.source = readout I v x) :
    R3.input.profile.logVolume O.source =
      I.sourceQPilotLogVolume v R n := by
  have hq := h (qMark I v R n)
  rw [readout_qMark] at hq
  exact hq

#check S2480ValueLayerToActualOutputRequired
#check s2480_profile_eq_sourceQPilot_of_map
#check s2480_constant_map_compat_forces_S2404

end LeanFormal.IUT.XiFPaper.S2480ValueLayerToActualOutputRequired
end
