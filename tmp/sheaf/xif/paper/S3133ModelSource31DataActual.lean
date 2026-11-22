import tmp.sheaf.xif.paper.S3136SourceDefinition31DataAssemblyAdapterActual

/-!
# Model SourceDefinition31Data assembly adapter (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model assembly,
mainline/lattice in-model R1 record.

Wires stage4's eight-slot SourceDefinition31Data assembly adapter to the
from-scratch model: the model source contract is the deterministic assembly of
the slot providers, with the concrete Gaussian arithmetic and the model
selected/bad place types.  The exact remaining providers (torsion/orbicurve/
sections/cusp and the five compatibility pairs) come from
S3136ModelSourceClauseInventoryActual statuses; those slots are model-side
provider data, not assumptions hidden in this file.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelSource31DataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual

variable {l : PrimeGeFive}

/-- Model source Definition 3.1 data: deterministic assembly from the model slot
providers. -/
def modelSource31Data (P : LGPSource31SlotProviders l) : SourceDefinition31Data l :=
  lgpSourceDefinition31Data_of_slots P

/-- The model source data's arithmetic is the provider arithmetic. -/
theorem modelSource31Data_arithmetic (P : LGPSource31SlotProviders l) :
    (modelSource31Data P).arithmetic = P.arithmetic :=
  lgpSourceDefinition31Data_of_slots_arithmetic P

/-- The model source data's selected/bad place slots are the provider slots. -/
theorem modelSource31Data_selectedPlaces (P : LGPSource31SlotProviders l) :
    (modelSource31Data P).selectedPlaces = P.selectedPlaces :=
  rfl

end LeanFormal.IUT.XiFPaper.S3133ModelSource31DataActual
