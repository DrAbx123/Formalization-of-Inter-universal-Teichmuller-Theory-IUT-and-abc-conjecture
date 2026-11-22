import tmp.sheaf.xif.paper.OneColumnActual
import tmp.sheaf.xif.paper.QPilotObjectFromSource

/-!
# Actual paper one-column label binding for the q-pilot object

Task-550 builds the actual paper 1,circ label binding for the q-pilot object,
using the existing actual modules:

* OneColumnActual: the actual one-column arithmetic holomorphic structure over
  the finite places of a number field (provided by
  sourceOneColumnActual / sourceOneColumnStructureOfNumberField);
* QPilotObjectActual / QPilotObjectFromSource: the actual paper q-pilot object
  at (1,0) built from source C1/C2/C3, the actual canonical times-mu strip, and
  the actual one-column structure.

The paper label 1,circ is bound by the actual column index carried by the
q-pilot object's (1,0) binding: n = P.oneZero.n = 1.  The carrier is the actual
SourceOneColumnArithmeticHolomorphicStructure already stored in P.oneColumn.
No separate toy label type or abstract index carrier is introduced.

For the actual finite-place carrier V = NumberField.FinitePlace k, the
one-column carrier is definitionally the actual
sourceOneColumnActual k = sourceOneColumnStructureOfNumberField k, so the label
binding is constructed from source data, not assumed.

No True/PUnit/axiom/sorry or arbitrary label is used.  The source data C1/C2/C3
are explicit inputs; this file constructs the label binding once they are
supplied.  This is write-only; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.PaperOneColumnLabelActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

universe ua uv upi umon ui uC3 uD3

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual paper 1,circ label binding for a q-pilot object P.

The label part is the actual integer column index n of P's (1,0) binding, with
the proof n = 1.  The carrier part is the actual one-column arithmetic
holomorphic structure P.oneColumn, with an equality field binding the label
carrier to it.  No abstract label carrier is introduced. -/
structure PaperOneColumnLabelActual
    (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)) where
  /-- The actual column index read from the q-pilot (1,0) binding. -/
  n : Int
  /-- The paper 1,circ label: the column index is 1. -/
  n_eq : n = 1
  /-- The actual one-column arithmetic holomorphic carrier. -/
  carrier : SourceOneColumnArithmeticHolomorphicStructure V
  /-- The label carrier is exactly the q-pilot object's one-column carrier. -/
  carrier_eq : carrier = P.oneColumn

namespace PaperOneColumnLabelActual

variable {P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)}

/-- The actual 1,circ label binding constructed from the q-pilot object's own
(1,0) index and one-column carrier.  This uses no arbitrary label. -/
def ofQPilot
    (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)) :
    PaperOneColumnLabelActual P where
  n := P.oneZero.n
  n_eq := P.oneZero_n
  carrier := P.oneColumn
  carrier_eq := rfl

/-- The bound column index is 1. -/
theorem ofQPilot_n_eq_one
    (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)) :
    (ofQPilot P).n = 1 :=
  (ofQPilot P).n_eq

/-- The bound carrier is the q-pilot object's actual one-column carrier. -/
theorem ofQPilot_carrier_eq
    (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)) :
    (ofQPilot P).carrier = P.oneColumn :=
  (ofQPilot P).carrier_eq

/-! ## Finite-place actual carrier -/

variable {k : Type} [Field k] [NumberField k]
variable (J : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))

/-- The actual q-pilot object on the finite-place carrier, from source C1/C2/C3. -/
abbrev finitePlaceQPilot
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    PaperQPilotObjectActual.{ua, 0, upi, umon, ui, uC3, uD3} (I := J) :=
  paperQPilotObjectOfNumberFieldSource J C1 C2 C3

/-- The actual 1,circ label binding on the finite-place carrier, from source
C1/C2/C3 and the actual one-column structure. -/
def finitePlaceLabel
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    PaperOneColumnLabelActual (finitePlaceQPilot J C1 C2 C3) :=
  ofQPilot (finitePlaceQPilot J C1 C2 C3)

/-- The finite-place label's carrier is the actual one-column structure
sourceOneColumnActual k. -/
theorem finitePlaceLabel_carrier_eq_source
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    (finitePlaceLabel J C1 C2 C3).carrier =
      sourceOneColumnActual (k := k) := rfl

/-- The finite-place label's column index is 1. -/
theorem finitePlaceLabel_n_eq_one
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    (finitePlaceLabel J C1 C2 C3).n = 1 :=
  (finitePlaceLabel J C1 C2 C3).n_eq

/-- The finite-place label's carrier is the q-pilot object's one-column
carrier. -/
theorem finitePlaceLabel_carrier_eq_qPilot
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    (finitePlaceLabel J C1 C2 C3).carrier =
      (finitePlaceQPilot J C1 C2 C3).oneColumn :=
  (finitePlaceLabel J C1 C2 C3).carrier_eq

end PaperOneColumnLabelActual

end LeanFormal.IUT.N8Closure.PaperOneColumnLabelActual
