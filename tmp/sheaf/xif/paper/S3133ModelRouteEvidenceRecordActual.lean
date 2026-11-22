import tmp.sheaf.xif.paper.S3133M2aClosedActual
import tmp.sheaf.xif.paper.S3133GaussianModelMapResidualFinalActual
import tmp.sheaf.xif.paper.S3133ExistingModelAdaptationActual
import tmp.sheaf.xif.paper.S3133M1ConcretePrimeMatchActual
import tmp.sheaf.xif.paper.S3133M1IndexIdentificationActual
import tmp.sheaf.xif.paper.S3133ModelRouteM1StatusActual
import tmp.sheaf.xif.paper.S3133ModelRouteM2bStatusActual
import tmp.sheaf.xif.paper.S3133ModelRouteR1StatusActual
import tmp.sheaf.xif.paper.S3135TreeModelBaseUnitScalingActual

/-!
# Model-route evidence record (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice FINAL-STATUS,
shehdd reopen checklist, Lead.

Single citable evidence record for the model route (registry frozen 14041; no
reopen claims here): lists the citable evidence ids and bundles the proved
status facts:
* M2a closed (S3133GaussianCanonicalQNorm_holds);
* R1 minimal-residual interface = M1 + M2b (S3133GaussianModelMapResidualFinalActual);
* in-model M1 placeToMod datum (S3133ModelRouteM1Status_holds);
* in-model M2b definitional qVFamily descent (S3133ModelRouteM2bStatus_holds);
* nontrivial baseUnit = -1 witness (abc S3135TreeModelBaseUnitScalingActual);
* concrete-donor TensorIndexPlaceCompatibility and index identification reduction
  (S3133M1ConcretePrimeMatchActual / S3133M1IndexIdentificationActual).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ModelRouteEvidenceRecordActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
open LeanFormal.IUT.XiFPaper.S3133M2aClosedActual
open LeanFormal.IUT.XiFPaper.S3133ModelRouteM1StatusActual
open LeanFormal.IUT.XiFPaper.S3133ModelRouteM2bStatusActual
open LeanFormal.IUT.XiFPaper.S3133ModelRouteR1StatusActual
open LeanFormal.IUT.XiFPaper.S3133ExistingModelAdaptationActual
open LeanFormal.IUT.XiFPaper.S3135TreeModelBaseUnitScalingActual

/-- Citable model-route evidence ids (for FINAL-STATUS/ledger records). -/
def S3133ModelRouteEvidenceIds : List String :=
  [ "S3133M2aNormReductionActual (EXIT0, checker CITABLE)",
    "S3133M2aClosedActual (EXIT0, checker CITABLE, 6 decls)",
    "S3133GaussianModelMapResidualFinalActual (EXIT0, checker CITABLE, R1 = M1+M2b interface)",
    "S3133ExistingModelAdaptationActual (EXIT0, checker CITABLE, 9 decls, Option-B tree-model adaptation)",
    "S3133M1ConcretePrimeMatchActual (EXIT0, checker CITABLE, 5 decls)",
    "S3133M1IndexIdentificationActual (EXIT0, checker CITABLE, 4 decls)",
    "S3133ModelRouteM1StatusActual (EXIT0, checker CITABLE)",
    "S3133ModelRouteM2bStatusActual (EXIT0, checker CITABLE)",
    "S3133ModelRouteR1StatusActual (EXIT0, checker CITABLE)",
    "S3133FrozenDonorResidualStatementsActual (EXIT0, exact frozen-donor R1 residual statements)",
    "S3135TreeModelBaseUnitScalingActual (abc, EXIT0, nontrivial baseUnit = -1)" ]

/-- Bundled model-route evidence status. -/
def S3133ModelRouteEvidenceStatus : Prop :=
  S3133GaussianCanonicalQNorm ∧ S3133ModelRouteM1Status ∧
    S3133ModelRouteM2bStatus ∧ Nonempty S3133TreeModelBaseUnitScaling

/-- The bundled model-route evidence status holds. -/
theorem S3133ModelRouteEvidenceStatus_holds : S3133ModelRouteEvidenceStatus :=
  ⟨S3133GaussianCanonicalQNorm_holds, S3133ModelRouteM1Status_holds,
    S3133ModelRouteM2bStatus_holds, ⟨s3135_treeModelBaseUnitScaling⟩⟩

end LeanFormal.IUT.XiFPaper.S3133ModelRouteEvidenceRecordActual
