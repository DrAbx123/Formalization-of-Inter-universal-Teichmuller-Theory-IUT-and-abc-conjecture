import tmp.sheaf.xif.paper.Mzk1C0IdeleHeightActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-!
# C0 readout identification interface

Conditional interface only.  Sign convention: `c0IdeleHeight` is the
nonnegative height, so the signed C0 log-volume is `-c0IdeleHeight`; this
readout is required to equal `-hBox` under component identification and to
equal the actual S3137 q-pilot reading `qPilotLogVolumeReading P` (which is
`-|log q| <= 0`).  No inhabitant is constructed; this records the exact second
missing arrow (idele -> signed global log-volume/readout).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C0ReadoutIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1C0GlobalIdeleActual
open LeanFormal.IUT.XiFPaper.Mzk1C0IdeleHeightActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.IUTIV.Estimates

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure C0ReadoutIdentification
    {V : Type} {I : OriginalInput l V}
    (P : PaperQPilotObjectActual (l := l) (I := I)) where
  readout : C0GlobalIdeleData T → Real
  readout_eq_neg_hBox : ∀ (D : C0GlobalIdeleData T) (x : T.arithmetic.F),
    C0HeightComponents T D x → readout D = -hBox (F := T.arithmetic.F) x
  readout_eq_qPilot : ∀ (D : C0GlobalIdeleData T),
    readout D = qPilotLogVolumeReading P

#check C0ReadoutIdentification

end LeanFormal.IUT.XiFPaper.Mzk1C0ReadoutIdentificationActual
