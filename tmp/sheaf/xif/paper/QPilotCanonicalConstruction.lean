import tmp.sheaf.xif.paper.QPilotIdentificationActual
import tmp.sheaf.xif.paper.QPilotObjectActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding

/-! # Canonical construction of the q-pilot identification data

Given an actual q-pilot line package and an actual one-column structure, this
file constructs `PaperQPilotObjectActual` with the canonical times-mu
prime-strip and the canonical (1,0) binding, and then constructs
`QPilotIdentificationActual` with all strip/one-column/log-Kummer/(1,0)
identifications by `rfl`. The one-column structure remains an actual source
parameter; no PUnit/True/axiom/sorry.
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

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Construct the actual q-pilot object with a supplied strip and one-column
structure. -/
def paperQPilotObjectActualOfLine
    (L : QPilotLineActual (I := I))
    (strip : SourceFTimesMuPrimeStrip.{uv, uM, uP} V)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    PaperQPilotObjectActual (I := I) where
  line := L
  strip := strip
  oneColumn := oneColumn
  logKummer := L.C2
  logKummer_eq := rfl
  oneZero := oneZeroPoint
  oneZero_eq := rfl

/-- Construct the actual q-pilot object with the canonical times-mu strip. -/
def paperQPilotObjectActualOfCanonical
    (L : QPilotLineActual (I := I))
    (F : FPrimeStrip V)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    PaperQPilotObjectActual (I := I) :=
  paperQPilotObjectActualOfLine L
    (SourceFTimesMuPrimeStrip.canonical F) oneColumn

namespace PaperQPilotObjectActual

variable (P : PaperQPilotObjectActual (I := I))

theorem strip_eq_supplied {strip : SourceFTimesMuPrimeStrip V}
    (h : P.strip = strip) : P.strip = strip := h

end PaperQPilotObjectActual

end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
end