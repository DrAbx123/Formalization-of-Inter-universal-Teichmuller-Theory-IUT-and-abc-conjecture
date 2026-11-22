import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import tmp.sheaf.xif.paper.S3133M1ConcretePrimeMatchActual
import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual

/-!
# Model-route M1 status: in-model placeToMod + concrete donor prime match
(component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice in-model R1
record, shehdd 3rd-reopen checklist.

Bundles the two green M1 outputs of the model route:
* on the EXISTING tree model (V = Unit) an explicit place-to-moduli datum with
  injective place map is constructed (S3133ExistingModelAdaptationActual);
* on the CONCRETE Gaussian donor (tensorIndex := Bad, refl equivalence) the
  prime-level TensorIndexPlaceCompatibility closes whenever all bad base places
  lie above 5 (S3133M1ConcretePrimeMatchActual; the hypothesis is the concrete
  stage-4 fact packet_rationalPrime_eq_five), and the exact remaining donor
  field is the index identification C3.tensorIndex = Bad (...).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelRouteM1StatusActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133M1ConcretePrimeMatchActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- In-model M1 on the existing tree model: explicit placeToMod datum with
injective place map. -/
theorem S3133ModelRouteM1_treeModel_constructible :
    ∃ D : S3133TreeModelPlaceToModDatum, Function.Injective D.placeOf :=
  S3133TreeModelM1_constructible

/-- Model-route M1 status: an explicit in-model placeToMod datum with
injective place map is constructed on the existing tree model.  The concrete
donor's prime-level match is proved separately in S3133M1ConcretePrimeMatchActual. -/
def S3133ModelRouteM1Status : Prop :=
  ∃ D : S3133TreeModelPlaceToModDatum, Function.Injective D.placeOf

/-- The model-route M1 status holds. -/
theorem S3133ModelRouteM1Status_holds : S3133ModelRouteM1Status :=
  S3133ModelRouteM1_treeModel_constructible

end LeanFormal.IUT.XiFPaper.S3133ModelRouteM1StatusActual
