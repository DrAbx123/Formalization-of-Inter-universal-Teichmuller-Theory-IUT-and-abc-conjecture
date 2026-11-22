import tmp.sheaf.xif.paper.S3137R1ThetaHalfConsumerActual

/-!
# S3137: Theta-half consumer aliases (task-53 delivery to hull/shehdd)

Short aliases of the green Theta-half readout declarations for hull/shehdd
consumers of the C3 packet normalization.  Raw-readout conventions are
documented at the declaration sites; no comparison is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137R1ThetaConsumerAliasActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaAliasMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaAliasBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Theta reading is the logarithm of the actual paper-hull Haar readout. -/
theorem theta_readout_eq_log_paperHull :
    thetaPilotHullLogVolumeReal C3 = Real.log (paperHullRealLogVolume C3) :=
  thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume C3

/-- Packaged ENNReal Theta reading is ofReal(log) of the paper-hull Haar readout. -/
theorem theta_readout_ennreal_eq :
    thetaPilotHullLogVolume C3 =
      ENNReal.ofReal (Real.log (paperHullRealLogVolume C3)) :=
  thetaPilotHullLogVolume_eq_ofReal_log_paperHullRealLogVolume C3

/-- Finiteness of the paper-hull Haar readout. -/
theorem paperHull_haar_readout_lt_top : paperHullHaarReadout C3 < ⊤ :=
  paperHullHaarReadout_lt_top C3

end LeanFormal.IUT.XiFPaper.S3137R1ThetaConsumerAliasActual

#check LeanFormal.IUT.XiFPaper.S3137R1ThetaConsumerAliasActual.theta_readout_eq_log_paperHull
#check LeanFormal.IUT.XiFPaper.S3137R1ThetaConsumerAliasActual.theta_readout_ennreal_eq
