import tmp.sheaf.xif.paper.S3132ThetaNormalizationFactorActual
import tmp.sheaf.xif.paper.S3137R1ThetaHalfConsumerActual

/-!
# S3137: Theta-half raw-readout / normalization-factor tie (task-53 delivery)

Consumer: hull's Theta-half normalization channel and shehdd's canonical rooted
Theta target.  The lattice Theta reading is the logarithm of the actual
paper-hull Haar mass (S3132R1ThetaHalfBridgeActual plus
S3137R1ThetaHalfConsumerActual); hull's S3132ThetaNormalizationFactorActual
identifies it with the raw C3 Haar log-volume `c3ThetaRawHaarLogVolume` and
exposes the exact degree-normalization factor
`thetaNormalizationFactor C3 = log mu(hull) - V(hull)`.

This file records:
* Real.log (paperHullRealLogVolume C3) = c3ThetaRawHaarLogVolume C3;
* if thetaNormalizationFactor C3 = 0, then the log of the paper-hull Haar
  readout equals the degree-normalized V-form log-volume of the actual paper
  hull.

Normalization caveat explicit: thetaPilotHullLogVolumeReal is the raw log-Haar
reading; the paper/fourth-triangle signed readout is degree-normalized V-form,
so these ties are the channel between the two, not a raw equality claim.
Source: IUT III, Prop. 3.9, (i), p. 115; Remark 3.9.5, (i), (ii), pp. 158-160;
IUT IV, Prop. 1.4, (i).  No inequality, no carrier.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137ThetaHalfNormalizationTieActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3132R1ThetaHalfBridgeActual
open LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3137R1ThetaHalfConsumerActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaTieMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance thetaTieBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The logarithm of the actual paper-hull Haar readout is hull's raw C3 Haar
log-volume expression. -/
theorem log_paperHullRealLogVolume_eq_c3ThetaRawHaarLogVolume :
    Real.log (paperHullRealLogVolume C3) = c3ThetaRawHaarLogVolume C3 := by
  rw [← thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume]
  exact thetaPilotHullLogVolumeReal_eq_c3ThetaRawHaarLogVolume C3

/-- **Factor-zero channel**: if the exact normalization factor vanishes, the
logarithm of the actual paper-hull Haar readout equals the degree-normalized
V-form log-volume of the actual paper hull. -/
theorem log_paperHullRealLogVolume_eq_c3NormalizedLogVolume_of_factor_zero
    (hfac : thetaNormalizationFactor C3 = 0) :
    Real.log (paperHullRealLogVolume C3) =
      c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3)) := by
  rw [← thetaPilotHullLogVolumeReal_eq_log_paperHullRealLogVolume]
  exact (thetaNormalizationFactor_eq_zero_iff C3).mp hfac

end LeanFormal.IUT.XiFPaper.S3137ThetaHalfNormalizationTieActual

#check LeanFormal.IUT.XiFPaper.S3137ThetaHalfNormalizationTieActual.log_paperHullRealLogVolume_eq_c3ThetaRawHaarLogVolume
#check LeanFormal.IUT.XiFPaper.S3137ThetaHalfNormalizationTieActual.log_paperHullRealLogVolume_eq_c3NormalizedLogVolume_of_factor_zero
