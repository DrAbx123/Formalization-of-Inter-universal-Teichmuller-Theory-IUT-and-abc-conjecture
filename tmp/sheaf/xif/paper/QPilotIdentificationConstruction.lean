import tmp.sheaf.xif.paper.QPilotIdentificationActual
import tmp.sheaf.xif.paper.QPilotCanonicalConstruction

/-! # Canonical q-pilot identification data

Constructs `QPilotIdentificationActual` with the canonical times-mu strip,
a supplied actual one-column structure, the actual C2 log-Kummer data and
the canonical (1,0) binding. All structural identifications are rfl.
No PUnit/True/axiom/sorry; the one-column structure remains an actual
source parameter.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

universe ua uv upi umon ui uM uP

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Canonical q-pilot identifications from actual line data. -/
def qPilotIdentificationActualOfCanonical
    (L : QPilotLineActual (I := I))
    (F : FPrimeStrip V)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    QPilotIdentificationActual I where
  object := paperQPilotObjectActualOfCanonical L F oneColumn
  canonicalStrip := SourceFTimesMuPrimeStrip.canonical F
  strip_eq := rfl
  canonicalOneColumn := oneColumn
  oneColumn_eq := rfl
  canonicalLogKummer := L.C2
  logKummer_eq := rfl
  canonicalOneZero := oneZeroPoint
  oneZero_eq := rfl

end LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual
end