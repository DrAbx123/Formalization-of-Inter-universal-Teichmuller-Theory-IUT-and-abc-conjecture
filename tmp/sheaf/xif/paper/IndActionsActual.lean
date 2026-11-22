import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.n8.closure.C4IndActionDataActualAttempt
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge
import tmp.sheaf.n8.closure.SourceWitnessedOutput

/-! # Actual IndActionData for the paper missing-ledger

The paper unconditional ledger records `PaperIndActionsMissing` as a
proposition. The actual C4 witnessed-output data carries an actual
`IndActionData` on its own ThetaPilotPoint carrier. This file inhabits the
missing-ledger proposition at that actual carrier.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C4IndActionDataActualAttempt
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The exact paper IndAction ledger is inhabited at the actual C4 carrier. -/
theorem paperIndActionsMissing_actual
    (C4 : SourceWitnessedOutputData I
      (Multiplicative (finiteLabel l))) :
    PaperIndActionsMissing (I := I)
      (Label := Multiplicative (finiteLabel l)) C4.place.v := by
  exact ⟨c4IndActionDataOfC4 I C4⟩

end LeanFormal.IUT.XiFPaper