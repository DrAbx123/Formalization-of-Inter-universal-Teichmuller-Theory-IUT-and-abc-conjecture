import tmp.sheaf.xif.paper.OrigXiFPaperQPilotFromSourceLActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual

/-! # A946: bridge the L line-bundle carrier to the paper completion carrier

The L carrier of OrigXiFPaperQPilotFromSourceLActual is definitionally the
completion-localized trivial carrier of OrigXiFPaperQPilotObjectActual.
This supplies the missing paper_lineBundle_identification for the L object. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.A946LineBundleBridge

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))

/-- The L carrier equals the concrete completion carrier, by definition. -/
theorem sourceL_eq_completion :
    LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual.OrigXiFSourceLLineBundleCarrier
      (I := I) =
    LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperCompletionLineBundleCarrier
      (k := I.initial.arithmetic.Fmod) := rfl

/-- The L carrier satisfies the concrete paper line-bundle identification. -/
theorem sourceL_identified :
    LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperLineBundleIdentified
      (LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual.OrigXiFSourceLLineBundleCarrier
        (I := I)) := by
  rw [sourceL_eq_completion]
  exact LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperCompletionLineBundleCarrier_identified

end LeanFormal.IUT.XiFPaper.A946LineBundleBridge
