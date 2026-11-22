import tmp.sheaf.xif.paper.ArithmeticLineBundleActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on QPilotLineBundleSourceData. The global q-pilot ideal/line-bundle identification is missing.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# q-pilot line bundle from actual source data: construction attempt

Task-558 attempts to construct PaperQPilotLineBundleSource from the actual
q-pilot object / C3 q parameter / local L-values or source arithmetic, reusing
ArithmeticLineBundleActual and OModuleActual.

The source audit is negative for an unconditional q-pilot line bundle:

* ArithmeticLineBundleActual supplies the actual source arithmetic field
  A : InitialThetaArithmeticData l, the actual fractional-ideal line bundle
  SourceLineBundle A = FractionalIdeal O_K K, the actual unit line bundle, and
  the actual PaperArithmeticLineBundleActual packet.  It explicitly records that
  InitialThetaArithmeticData does not contain the q-pilot fractional ideal or
  its O-module class; the missing field is
  PaperQPilotLineBundleSource.qPilot_lineBundle_identification.
* SourcePilotRegionData (C3) supplies the local q
  q : FinitePlaceQCandidate place.val, the local unit
  qUnit : (CommonPrimeCompletion ...)^x, the local tensor unit, and local
  landing data.  It supplies no global fractional ideal
  FractionalIdeal O_K K and no global ideal Ideal O_K.
* Local L-values (Real) and the local qUnit are not a global O_K-line bundle;
  constructing a global ideal from them would be an extra source map.

Therefore the exact missing source map is a global q-pilot ideal and its
line-bundle identification:

  qPilotIdeal : Ideal (NumberField.RingOfIntegers A.K)
  qPilotLineBundle = (qPilotIdeal : FractionalIdeal ...)

This file constructs the conditional PaperQPilotLineBundleSource from exactly
that explicit data and records the actual unit-line-bundle packet separately.
No arbitrary ideal is chosen, and the unit line bundle is not substituted for
the q-pilot line bundle.  No True/PUnit/axiom/sorry is used.

WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.PaperQPilotLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable (A : InitialThetaArithmeticData l)

/-! ## 1. Actual source arithmetic unit-line-bundle packet -/

/-- The actual unit-line-bundle packet from the source arithmetic field.  This
is actual source arithmetic content, but it is deliberately not claimed to be
the q-pilot line bundle. -/
def actualSourceUnitLineBundle : PaperArithmeticLineBundleActual A :=
  actualUnitLineBundleData (A := A)

@[simp] theorem actualSourceUnitLineBundle_lineBundle :
    (actualSourceUnitLineBundle A).lineBundle = unitLineBundle (A := A) := rfl

/-! ## 2. Exact conditional q-pilot line bundle from a global ideal -/

/-- The exact source data needed for PaperQPilotLineBundleSource: a global
q-pilot ideal and the proposition identifying it with the q-pilot source line
bundle.  This is an input record, not an arbitrary ideal. -/
structure QPilotLineBundleSourceData where
  qPilotIdeal : Ideal (SourceOK (A := A))
  qPilot_source_identification : Prop

/-- The conditional PaperQPilotLineBundleSource constructed from the exact
global q-pilot ideal field.  The line bundle is the fractional ideal generated
by qPilotIdeal; the identification proposition is carried explicitly. -/
noncomputable def qPilotLineBundleSourceOfData
    (D : QPilotLineBundleSourceData A) :
    PaperQPilotLineBundleSource A where
  qPilotLineBundle :=
    (D.qPilotIdeal : FractionalIdeal (nonZeroDivisors (SourceOK (A := A))) A.K)
  qPilotIdeal := D.qPilotIdeal
  qPilot_lineBundle_eq := rfl
  qPilot_source_identification := D.qPilot_source_identification

/-- The conditional constructor has the supplied q-pilot ideal. -/
theorem qPilotLineBundleSourceOfData_ideal
    (D : QPilotLineBundleSourceData A) :
    (qPilotLineBundleSourceOfData A D).qPilotIdeal = D.qPilotIdeal := rfl

/-- The line bundle of the conditional constructor is the fractional ideal of
the supplied q-pilot ideal. -/
theorem qPilotLineBundleSourceOfData_lineBundle
    (D : QPilotLineBundleSourceData A) :
    (qPilotLineBundleSourceOfData A D).qPilotLineBundle =
      (D.qPilotIdeal : FractionalIdeal
        (nonZeroDivisors (SourceOK (A := A))) A.K) := rfl

/-! ## 3. Exact missing source map -/

/-- Exact missing source map: a global q-pilot ideal with its line-bundle
identification.  The source arithmetic field alone supplies only the unit line
bundle, not this datum. -/
def MissingQPilotLineBundleSource (A : InitialThetaArithmeticData l) : Prop :=
  Nonempty (QPilotLineBundleSourceData A)

/-- The exact missing map in the original PaperQPilotLineBundleSource shape. -/
def MissingQPilotLineBundleIdentification (A : InitialThetaArithmeticData l) : Prop :=
  ∃ qPilotIdeal : Ideal (SourceOK (A := A)),
    ∃ qPilot_source_identification : Prop,
      Nonempty (PaperQPilotLineBundleSource A)

/-! ## 4. What is and is not constructed

The actual source arithmetic unit line bundle is constructed above.  The
q-pilot line bundle itself is not: the C3 q is local (completion element/unit),
and no global ideal map is present.  The conditional constructor is the exact
source-map obligation.  No unit-ideal/trivial line-bundle substitution is made.
-/

/-- The actual source arithmetic unit line bundle is not asserted to be the
q-pilot line bundle.  This is only the source arithmetic packet. -/
theorem actualSourceUnitLineBundle_is_sourceArithmetic :
    (actualSourceUnitLineBundle A).lineBundle = unitLineBundle (A := A) := rfl

/-- The missing global q-pilot ideal map is exactly the conditional input. -/
theorem missingQPilotLineBundleSource_iff_conditional :
    MissingQPilotLineBundleSource A ↔
      Nonempty (QPilotLineBundleSourceData A) := Iff.rfl

end LeanFormal.IUT.N8Closure.PaperQPilotLineBundleActual
