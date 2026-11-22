import tmp.sheaf.xif.paper.QPilotIdentificationConstruction
import tmp.sheaf.xif.paper.QPilotCanonicalConstruction
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism

/-! # Actual one-column structure for the number-field finite-place carrier

For `V = NumberField.FinitePlace k`, the actual one-column arithmetic
holomorphic structure is `sourceOneColumnStructureOfNumberField k`. This
closes the one-column parameter of the canonical q-pilot construction on the
actual finite-place carrier. The paper label `1,circ` binding remains the
separate source obligation.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding

universe ua uv upi umon ui uM uP

variable {l : PrimeGeFive}

/-- The actual one-column structure over finite places of a number field. -/
def sourceOneColumnActual (k : Type) [Field k] [NumberField k] :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace k) :=
  sourceOneColumnStructureOfNumberField k

variable {k : Type} [Field k] [NumberField k]
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))

/-- The q-pilot line package on the actual finite-place carrier. -/
abbrev NumberFieldQPilotLine := QPilotLineActual (l := l) (V := NumberField.FinitePlace k) I

/-- Actual q-pilot object on the finite-place carrier, using the actual
one-column structure and the canonical times-mu strip of the input strip. -/
def paperQPilotObjectActualOfNumberField
    (L : QPilotLineActual (l := l) (V := NumberField.FinitePlace k) I) :
    PaperQPilotObjectActual (l := l) (V := NumberField.FinitePlace k) I :=
  paperQPilotObjectActualOfCanonical L
    (I.primeStripAt 0 0)
    (sourceOneColumnActual k)

/-- The corresponding actual q-pilot identification data. -/
def qPilotIdentificationActualOfNumberField
    (L : QPilotLineActual (l := l) (V := NumberField.FinitePlace k) I) :
    LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.QPilotIdentificationActual I :=
  LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.qPilotIdentificationActualOfCanonical
    L (I.primeStripAt 0 0) (sourceOneColumnActual k)

end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
end