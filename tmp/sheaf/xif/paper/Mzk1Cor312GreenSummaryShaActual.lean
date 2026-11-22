import tmp.sheaf.xif.paper.Mzk1Cor312PaperReadoutConsumerActual
import tmp.sheaf.xif.paper.Mzk1Cor312SignedMagnitudeChecksActual

/-!
# A574 GreenSummary (shehdd resolved-acceptance green facts)

Structure bundling the green actual-reading facts consumed by ABC Stage-5:
* finiteness of the actual Theta hull measure;
* nonpositivity of the actual q reading (`-|log q| <= 0`);
* the signed/magnitude equivalence.

All fields are actual proofs from green modules.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312GreenSummaryShaActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperReadoutConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312SignedMagnitudeChecksActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
local instance greenSummaryMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance greenSummaryBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

structure GreenSummary where
  thetaHull_finite : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤
  signed_magnitude : ∀ {qMag thetaMag : Real},
    -thetaMag ≤ -qMag ↔ qMag ≤ thetaMag

/-- Nonpositivity of the actual q reading (standalone, avoids structure-universe issues). -/
theorem greenSummary_qReading_nonpos (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P ≤ 0 :=
  qPilotLogVolumeReading_nonpos P

noncomputable def greenSummary : GreenSummary C3 where
  thetaHull_finite := thetaPilotHull_measure_lt_top (C3 := C3)
  signed_magnitude := fun {_ _} => signed_ineq_iff_magnitude'

end LeanFormal.IUT.XiFPaper.Mzk1Cor312GreenSummaryShaActual
