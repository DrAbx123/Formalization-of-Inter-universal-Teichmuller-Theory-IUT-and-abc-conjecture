import tmp.sheaf.xif.paper.OneColumnActual
import tmp.sheaf.xif.paper.QPilotCanonicalConstruction

/-! # Paper q-pilot object from actual source C1/C2/C3

This file constructs QPilotLineActual and PaperQPilotObjectActual from the
actual source fields:

* C1 : SourceInputBinding I;
* C2 : SourceLogKummerData I C1;
* C3 : SourcePilotRegionData I.

The q-pilot line/rank-one data are exactly these fields.  The canonical
F^value x mu-prime-strip is the actual input prime strip I.primeStripAt 0 0.
The one-column arithmetic holomorphic structure is an explicit source field on
a general carrier V; on the actual finite-place carrier
V = NumberField.FinitePlace k it is supplied by OneColumnActual.sourceOneColumnActual.

No toy data/True/PUnit/axiom/sorry.  The no-inhabitant fields (C1/C2/C3 and,
on a general V, oneColumn) remain explicit source inputs. -/

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

universe ua uv upi umon ui uM uP uC3 uD3

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual q-pilot line/rank-one data from source C1/C2/C3. -/
def qPilotLineOfSource
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3}
      (l := l) (V := V) I) :
    QPilotLineActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I) where
  C1 := C1
  C2 := C2
  C3 := C3

/-- The line data's C1 is the supplied source binding. -/
@[simp] theorem qPilotLineOfSource_C1
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I) :
    (qPilotLineOfSource C1 C2 C3).C1 = C1 := rfl

/-- The line data's C2 is the supplied Kummer data. -/
@[simp] theorem qPilotLineOfSource_C2
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I) :
    (qPilotLineOfSource C1 C2 C3).C2 = C2 := rfl

/-- The line data's C3 is the supplied pilot-region data. -/
@[simp] theorem qPilotLineOfSource_C3
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I) :
    (qPilotLineOfSource C1 C2 C3).C3 = C3 := rfl

/-- The actual q-pilot object from source C1/C2/C3, the canonical
times-mu strip of the input prime strip, and an explicit one-column structure.
On a general V the one-column structure is the exact missing source field. -/
def paperQPilotObjectOfSource
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I) :=
  paperQPilotObjectActualOfCanonical
    (qPilotLineOfSource C1 C2 C3)
    (I.primeStripAt 0 0)
    oneColumn

/-- The constructed object's line is the supplied source line. -/
@[simp] theorem paperQPilotObjectOfSource_line
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    (paperQPilotObjectOfSource C1 C2 C3 oneColumn).line =
      qPilotLineOfSource C1 C2 C3 := rfl

/-- The constructed object's log-Kummer data is C2. -/
@[simp] theorem paperQPilotObjectOfSource_logKummer
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    (paperQPilotObjectOfSource C1 C2 C3 oneColumn).logKummer = C2 := rfl

/-- The constructed object's (1,0) binding is canonical. -/
@[simp] theorem paperQPilotObjectOfSource_oneZero
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3} (l := l) (V := V) I)
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V) :
    (paperQPilotObjectOfSource C1 C2 C3 oneColumn).oneZero = oneZeroPoint := rfl

/-! ## Finite-place carrier: actual one-column structure

For V = NumberField.FinitePlace k, the one-column structure is supplied by
OneColumnActual.sourceOneColumnActual, so no one-column field is missing. -/

variable {k : Type} [Field k] [NumberField k]
variable (J : OriginalInput.{ua, 0, upi, umon, ui} l (NumberField.FinitePlace k))

/-- Actual q-pilot object on the finite-place carrier from source C1/C2/C3,
using the actual one-column structure. -/
def paperQPilotObjectOfNumberFieldSource
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    PaperQPilotObjectActual.{ua, 0, upi, umon, ui, uC3, uD3} (I := J) :=
  paperQPilotObjectActualOfNumberField J
    (qPilotLineOfSource C1 C2 C3)

/-- The finite-place construction has the canonical identification data. -/
def qPilotIdentificationOfNumberFieldSource
    (C1 : SourceInputBinding J)
    (C2 : SourceLogKummerData J C1)
    (C3 : SourcePilotRegionData.{ua, 0, upi, umon, ui, uC3, uD3}
      (l := l) (V := NumberField.FinitePlace k) J) :
    LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual.QPilotIdentificationActual
      (l := l) (V := NumberField.FinitePlace k) J :=
  qPilotIdentificationActualOfNumberField J
    (qPilotLineOfSource C1 C2 C3)

/-! ## Exact remaining source fields

On a general carrier V:

1. C1 : SourceInputBinding I;
2. C2 : SourceLogKummerData I C1;
3. C3 : SourcePilotRegionData I;
4. oneColumn : SourceOneColumnArithmeticHolomorphicStructure V.

On V = NumberField.FinitePlace k, only C1/C2/C3 remain; the one-column
structure is actual via OneColumnActual.sourceOneColumnActual.  No arbitrary
data/axiom/sorry is used and no unconditional object is fabricated. -/

end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

end
