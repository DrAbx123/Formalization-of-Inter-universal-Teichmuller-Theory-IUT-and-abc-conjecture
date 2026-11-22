import tmp.sheaf.xif.paper.S3133ModelSource31DataActual
import tmp.sheaf.xif.paper.S3133ModelM1PlaceToModActual

/-!
# Model SourceDefinition31Data wired with the constructed placeToMod
(component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot in-model R1 composition,
mainline/lattice model-route record.

The frozen SourceDefinition31Data has no placeToMod field (IUT I Def 3.1(b),(e)
data are supplied through the selection/restriction section).  For the
from-scratch model this file bundles stage4's eight-slot source data with the
constructed in-model place map (S3133ModelM1PlaceToModActual): the bundle is the
model's V_mod_bijection source datum, with faithfulness by construction.  No
field of the frozen structure is modified.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelSource31DataWithPlaceToModActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual
open LeanFormal.IUT.XiFPaper.S3133ModelSource31DataActual
open LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual

variable {l : PrimeGeFive}

/-- Model source data bundled with the constructed V_mod_bijection place map. -/
structure S3133ModelSource31DataWithPlaceToMod (l : PrimeGeFive) where
  /-- the eight-slot source contract providers (stage4 adapter) -/
  providers : LGPSource31SlotProviders l
  /-- the model V_mod_bijection source datum (IUT I Def 3.1(b),(e)) -/
  placeToMod : S3135ModelVMod → S3135ModelV
  /-- faithfulness of the model place map -/
  placeToMod_injective : Function.Injective placeToMod

/-- The bundled model source data. -/
def S3133ModelSource31DataWithPlaceToMod.sourceData
    (D : S3133ModelSource31DataWithPlaceToMod l) : SourceDefinition31Data l :=
  modelSource31Data D.providers

/-- The bundled model source data's place map is the constructed one with
faithfulness by construction (in-model M1 datum wired in). -/
noncomputable def modelSource31DataWithPlaceToMod
    (P : LGPSource31SlotProviders l) :
    S3133ModelSource31DataWithPlaceToMod l where
  providers := P
  placeToMod := modelPlaceToMod
  placeToMod_injective := modelPlaceToMod_injective

/-- The wired model place map is injective (M1 in-model datum). -/
theorem modelSource31DataWithPlaceToMod_injective
    (P : LGPSource31SlotProviders l) :
    Function.Injective (modelSource31DataWithPlaceToMod P).placeToMod :=
  modelSource31DataWithPlaceToMod P |>.placeToMod_injective

end LeanFormal.IUT.XiFPaper.S3133ModelSource31DataWithPlaceToModActual
