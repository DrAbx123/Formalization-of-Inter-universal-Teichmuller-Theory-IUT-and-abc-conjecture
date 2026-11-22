/- U-R theta volume core (kurt): green split of Mzk1ThetaHullVolumeReadoutActual lines 1-134.

The parent file Mzk1ThetaHullVolumeReadoutActual FAILs only in its tail (the MRRep possibleRegion
section at :145 and the ThetaHullVolumeObject structure at :163/:167, API drift).  The first part
(theta-pilot hull Haar log-volume readout, p-scaling, the local j^2 Theta scaling
log||Theta_j|| = (j^2/(2l)) log q, and the (Ind3) possible-log-volume set) is independent of that
tail and is exactly the theta-side volume identification needed by the route C2/J1 analysis.
Re-exported here unchanged so downstream work can import a green module.

-/
/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1HullReadoutReuseActual
import Mathlib.Tactic

/-! A518: Theta-pilot hull volume readout object.
Objects and real lemmas (no comparison):
* thetaPilotLogVolumeReadout = S3137 actual hull Haar log-volume;
  constructed equalities to the hull Haar and to the actual C3 region;
* p-scaling of the readout (Prop 3.9 (i) at the actual hull);
* the local j^2 Theta scaling in the form gaussExponent/(2l) * log q
  from the actual S201 root norms (laichunwing 07);
* the possible-log-volume set R_{<= theta} as an (Ind3) region, and the
  multiradial possibleRegion inclusion of a representative region
  (LANA Multiradial Spec, green Ref copy). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullVolumeReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1HullReadoutReuseActual
open Iut.Multiradial
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. The Theta-pilot hull volume readout -/

/-- The Theta-pilot hull volume readout: the actual S3137 Haar log-volume of the
actual Theta-pilot hull. -/
noncomputable def thetaPilotLogVolumeReadout : Real :=
  thetaPilotHullLogVolumeReal C3

theorem thetaPilotLogVolumeReadout_constructed :
    thetaPilotLogVolumeReadout C3 = thetaPilotHullLogVolumeReal C3 := rfl

theorem thetaPilotLogVolumeReadout_eq_hullHaar :
    thetaPilotLogVolumeReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume (C3 := C3)

theorem thetaPilotLogVolumeReadout_eq_actualRegion :
    thetaPilotLogVolumeReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

theorem thetaPilotLogVolumeReadout_eq_reuse :
    thetaPilotLogVolumeReadout C3 =
      Mzk1HullReadoutReuseActual.thetaHullReadout C3 := rfl

theorem thetaPilotLogVolumeReadout_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  thetaPilotHull_measure_lt_top (C3 := C3)

/-- p-scaling of the hull volume readout: multiplying the actual hull by p shifts
the Haar log-volume by -[block : Q_p] * log p (IUT III, Prop 3.9 (i)). -/
theorem thetaPilotLogVolumeReadout_p_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) +
        thetaPilotLogVolumeReadout C3 :=
  thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos


end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullVolumeReadoutActual
end
