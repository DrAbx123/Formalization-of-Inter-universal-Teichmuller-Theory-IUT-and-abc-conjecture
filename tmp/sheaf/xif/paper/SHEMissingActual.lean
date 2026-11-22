import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.PaperXiFUnconditional

/-! # Actual SHE landing datum for the paper missing-ledger

The paper unconditional ledger records `PaperSHEMissing` as a proposition.
The actual SHE landing construction gives an inhabitant for the actual
one-column structure and the actual integral-section output carrier.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source.SHELandingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper

/-- The actual SHE landing proposition is inhabited for the actual completion
one-column structure and the integral-section output carrier. -/
theorem paperSHEMissing_actual (k : Type) [Field k] [NumberField k] :
    PaperSHEMissing (oneColumnStructure (k := k)) (Output (k := k)) :=
  sourceLocalizationExpressible_integralSection (k := k) (1 : Output (k := k))

end LeanFormal.IUT.Theorem311Source.SHELandingActual