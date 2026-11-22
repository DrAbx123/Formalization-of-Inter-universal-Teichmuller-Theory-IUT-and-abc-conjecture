import tmp.sheaf.xif.paper.SHEAlgorithmFromSource
import tmp.sheaf.xif.paper.SHEOperationsFromSource
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.SHEOutputActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional: ProcessionChoice/Output alignment and SHE landing are explicit missing objects. No source-faithful equivalence is constructed.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# SHE output alignment for the actual ProcessionChoice algorithm output

The actual finite-kernel algorithm of SHEAlgorithmFromSource has output
carrier ProcessionChoice l. The actual SHE operation landing of
SHEOperationsFromSource has output carrier the integral sections Output k.
This file records the two exact alignment/landing primitives and proves what
follows from them. No equivalence or landing is fabricated.

Why no actual construction is available: there is no source map from
ProcessionChoice l to the integral sections O_k, and no actual SHE reading
of ProcessionChoice l into the completed local rings. The carrier types are
both countable but no source bijection/reading is supplied; choosing one by
Classical.choice would be arbitrary, not an actual construction.

No toy/True/PUnit/sorry/axiom. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {l : PrimeGeFive}

/-- Exact output-carrier alignment primitive: a nonempty equivalence between
 the actual algorithm output ProcessionChoice l and the SHE integral-section
 output carrier Output k. No such equivalence is produced by the source. -/
def OutputCarrierAlignment (k : Type) [Field k] [NumberField k] : Prop :=
  Nonempty (ProcessionChoice l ≃ SHELandingActual.Output (k := k))

/-- Exact SHE landing primitive for the actual algorithm output carrier: a
 SourceLocalizationExpression whose output carrier is ProcessionChoice l.
 This is not the integral-section landing over Output k. -/
def SHELandingForProcessionChoice (k : Type) [Field k] [NumberField k] : Prop :=
  SourceLocalizationExpressible (SHELandingActual.oneColumnStructure (k := k))
    (ProcessionChoice l)

/-- If an output-carrier equivalence and a SHE landing for the integral-section
 carrier are supplied, the ProcessionChoice landing follows by transport
 along the equivalence. This is the actual conditional bridge. -/
theorem sheLandingForProcessionChoice_of_alignment
    (k : Type) [Field k] [NumberField k]
    (e : ProcessionChoice l ≃ SHELandingActual.Output (k := k))
    (h : SourceLocalizationExpressible
      (SHELandingActual.oneColumnStructure (k := k))
      (SHELandingActual.Output (k := k))) :
    SHELandingForProcessionChoice (l := l) k := by
  classical
  rcases h with ⟨E⟩
  refine ⟨?_⟩
  refine { bundle := E.bundle,
           output := e.symm E.output,
           expression := fun v o => E.expression v (e o),
           isLocalizationReading := ?_ }
  intro v o
  exact E.isLocalizationReading v (e o)

/-- The actual algorithm output is ProcessionChoice l (from the constructed
 source algorithm); this is not the integral-section carrier. -/
theorem actualAlgorithmOutput_ne_integral_sections :
    ActualAlgorithmOutput (l := l) = ProcessionChoice l := rfl

/- Exact missing primitives:
1. OutputCarrierAlignment k: a nonempty equivalence
   ProcessionChoice l ≃ SHELandingActual.Output k.
2. SHELandingForProcessionChoice k: an actual SourceLocalizationExpressible
   for output carrier ProcessionChoice l.
No source map/reading between these carriers is present. The conditional
bridge theorem above shows what an alignment would give; no such equivalence
is asserted. No toy/axiom/sorry. -/

#check OutputCarrierAlignment
#check SHELandingForProcessionChoice
#check sheLandingForProcessionChoice_of_alignment
#check actualAlgorithmOutput_ne_integral_sections

end LeanFormal.IUT.Theorem311Source.SHEOutputAlignmentActual

end
