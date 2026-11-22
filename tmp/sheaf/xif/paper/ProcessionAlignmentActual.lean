import tmp.sheaf.xif.paper.SHEAlgorithmFromSource
import tmp.sheaf.xif.paper.SHELandingActual
import tmp.sheaf.xif.paper.SHEOutputAlignmentActual
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring

/-! # CONDITIONAL STATUS (xi-f)

Conditional on ProcessionAlignment; no source-faithful equivalence/reading is constructed.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# ProcessionChoice output alignment: actual attempt

The actual finite-kernel algorithm output is `ProcessionChoice l`, whose
fields are two `ZMod l.value` labels and a natural Ind3 level. The SHE output
carrier is `NumberField.RingOfIntegers k`. The source supplies no canonical
map between these carriers; cardinality is not the issue (both are countably
infinite), but no source-faithful reading or equivalence is constructed in the
source data. An equivalence chosen from countability would be arbitrary and is
not used.

This file records the exact alignment primitive and the conditional transport
of an actual integral-section landing along any supplied equivalence. It does
not assert the equivalence. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.ProcessionAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEAlgorithmFromSource
open LeanFormal.IUT.Theorem311Source.SHELandingActual
open LeanFormal.IUT.ConcreteFiniteTheorem311

variable {l : PrimeGeFive}

/-- Exact alignment primitive: a source-faithful equivalence between the actual algorithm output and the SHE integral-section output. -/
def ProcessionAlignment (k : Type) [Field k] [NumberField k] : Prop :=
  Nonempty (ProcessionChoice l ≃ Output (k := k))

/-- A supplied alignment plus the actual integral-section landing transports to a SHE landing for the actual algorithm output. -/
theorem processionalLanding_of_alignment
    (k : Type) [Field k] [NumberField k]
    (e : ProcessionChoice l ≃ Output (k := k))
    (h : SourceLocalizationExpressible (oneColumnStructure (k := k))
      (Output (k := k))) :
    SourceLocalizationExpressible (oneColumnStructure (k := k))
      (ProcessionChoice l) := by
  classical
  rcases h with ⟨E⟩
  refine ⟨{ bundle := E.bundle,
             output := e.symm E.output,
             expression := fun v o => E.expression v (e o),
             isLocalizationReading := ?_ }⟩
  intro v o
  exact E.isLocalizationReading v (e o)

/- Exact missing object: a source-faithful ProcessionAlignment k, i.e. an
actual map/equivalence between the finite-kernel ProcessionChoice output and
the integral-section carrier, or equivalently an actual SHE reading of
ProcessionChoice l into the completed local rings. Cardinality/denumerability
alone does not provide a source-faithful map; no Classical.choice equivalence
is inserted. -/

#check ProcessionAlignment
#check processionalLanding_of_alignment

end LeanFormal.IUT.Theorem311Source.ProcessionAlignmentActual

end
