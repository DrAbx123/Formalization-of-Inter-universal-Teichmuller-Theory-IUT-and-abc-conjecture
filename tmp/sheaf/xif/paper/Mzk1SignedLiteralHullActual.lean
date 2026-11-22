import tmp.sheaf.xif.paper.Mzk1MonotoneSignedDirectionActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Literal Theta-hull signed log-volume on the actual C3 Haar region

Connects the signed-log-volume containment lemma to the actual S3137 hull
readout.  `thetaPilotHull = actualC3LogShellTensorRegion`, and the signed
Haar log-volume of the hull is definitionally `thetaPilotHullLogVolumeReal`.
No comparison value is asserted; only the signed monotone interface. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedLiteralHullActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance : MeasurableSpace (C3LogShellTensorBlock C3) := borel _

def literalHullSignedLogVolume : Real :=
  signedLogVolume (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)

theorem literalHullSignedLogVolume_eq_reading :
    literalHullSignedLogVolume C3 = thetaPilotHullLogVolumeReal C3 := rfl

theorem literalHullSignedLogVolume_region_eq :
    literalHullSignedLogVolume C3 =
      signedLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) := by
  unfold literalHullSignedLogVolume
  rw [thetaPilotHull_eq_region]

theorem literalHullSignedLogVolume_le_of_subset
    {qRegion : Set (C3LogShellTensorBlock C3)}
    (hsub : qRegion ⊆ thetaPilotHull C3)
    (hq : 0 < (actualC3LogShellTensorHaar C3) qRegion)
    (hh : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) ≠ ⊤) :
    signedLogVolume (actualC3LogShellTensorHaar C3) qRegion ≤
      literalHullSignedLogVolume C3 :=
  signedLogVolume_mono (actualC3LogShellTensorHaar C3) hsub hq hh

end LeanFormal.IUT.XiFPaper.Mzk1SignedLiteralHullActual

end
