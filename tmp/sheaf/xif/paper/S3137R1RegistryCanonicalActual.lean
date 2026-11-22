import tmp.sheaf.xif.paper.S3131FinalResidualRegistryActual
import tmp.sheaf.xif.paper.S3137SameCModelMapResidualActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonSummaryActual
import tmp.sheaf.xif.paper.S3137GaussianR1ResidualLightActual
import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual

/-!
# S3137: canonical R1 registry overlay and gate import closure (task-53)

Registry dedupe (task-53): mainline's S3131FinalResidualRegistryActual entry
  R1.M2M3M5.sameC-q-theta-readout
is the canonical registry id for lattice's R1 bridge/residual.  This file
records the canonical mapping (no second abstract residual object):

* object: SameCQThetaReadoutBridge (two same-C readout equalities) and its named
  wrapper NativeToC3SameCReadoutIdentification, carried by the single Prop
  SameCModelMapResidual (M0-M5) with proved collapse/consumer theorems;
* reduced residual (qpilot minimal Gaussian model map): M0 and M3 PROVED
  (S3133GaussianModelMapResidualMinimal_m0/_m3); residual is exactly
  m1_indexInjection (source placeToMod provenance; IUT I Def 3.1(b),(e);
  III Prop 3.4(ii)) and m2_baseQMatch (clause-B base-q descent, Gaussian norm
  1/5 at bad places above 5; IUT I Ex 3.2(iv); III Def 3.8(i)), plus the
  readout-side M4/M5 equalities;
* consumers keep their dependsOn edge to this id (list below).

Gate import lines provided and verified by the imports above (all fresh olean,
EXIT=0):
  import tmp.sheaf.xif.paper.S3137SameCModelMapResidualActual
  import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
  import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
  import tmp.sheaf.xif.paper.S3137QThetaComparisonSummaryActual
  import tmp.sheaf.xif.paper.S3137GaussianR1ResidualLightActual
  import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual

No proof content is added here; registry/consumer data only.  WRITE-ONLY.
-/

namespace LeanFormal.IUT.Audit

/-- **Canonical R1 registry entry.**  Same id as mainline's registry; the note
is updated to the canonical object (SameCModelMapResidual / SameCQThetaReadoutBridge)
and the reduced residual after qpilot's minimal Gaussian model map (M0/M3
proved, residual m1+m2 + readout M4/M5). -/
def S3137R1RegistryCanonical : Obligation :=
  { id := "R1.M2M3M5.sameC-q-theta-readout"
    source := "IUT I Def 3.1, Ex 3.2(iv); IUT II Rem 2.5.1(i); IUT III Prop 3.4(ii) pp.102-103; Def 3.8(i) p.112; Prop 3.9(i) p.115; Remark 3.1.1(ii); IUT IV Prop 1.4(i); Cor 3.12"
    status := VerificationStatus.pending
    note := "CANONICAL id for lattice R1 bridge/residual.  Object: SameCQThetaReadoutBridge / NativeToC3SameCReadoutIdentification, carried by SameCModelMapResidual with proved collapse and signed+magnitude comparison consumers.  Reduced residual: M0/M3 PROVED via qpilot S3133GaussianModelMapResidualMinimal_m0/_m3; residual = m1_indexInjection (source placeToMod provenance, contract-separated) + m2_baseQMatch (clause-B base-q descent, Gaussian norm 1/5 above 5) + readout M4/M5 (task-40).  Consumers keep dependsOn edge to this id."
    dependsOn := ["R1.M0.native-to-OriginalInput", "R1.M1.bad-tensor-index", "canonical.normalized-2l-root-supply"] }

/-- **Consumer edges for the canonical R1 id.**  Consumers keep a dependsOn edge
to R1.M2M3M5.sameC-q-theta-readout instead of introducing duplicate residual
objects. -/
def S3137R1ConsumerEdges : List (String × List String) :=
  [ ("S3137QThetaComparisonBridgeActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3137NativeToC3SameCReadoutActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3137SameCModelMapResidualActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3137GaussianR1ResidualLightActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3132QThetaConsumerWiringActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3134MainlineRootedHFaActual", ["R1.M2M3M5.sameC-q-theta-readout"]),
    ("S3140ClosureGateActual", ["R1.M2M3M5.sameC-q-theta-readout"]) ]

/-- **Green consumer declarations (gate-checked by imports above).**  Every
declaration below is EXIT0 + fresh olean + trio probe. -/
def S3137R1GreenConsumers : List String :=
  [ "S3137QThetaComparisonBridgeActual.qThetaPilotLogVolumeComparison_of_sameC",
    "S3137QThetaComparisonBridgeActual.qThetaMagnitudeComparison_of_sameC",
    "S3137SameCModelMapResidualActual.nativeToC3Identification_of_modelMap",
    "S3137SameCModelMapResidualActual.qThetaPilotLogVolumeComparison_of_modelMap",
    "S3137NativeToC3SameCReadoutActual.qThetaPilotLogVolumeComparison_of_nativeIdentification",
    "S3137GaussianR1ResidualLightActual.gaussianR1ReducedResidual_residual_iff",
    "S3137QThetaComparisonSummaryActual.s3137_signed_comparison_summary",
    "S3137C3TensorBlockDimensionActual.c3TensorBlockDimension_eq_prod_finrank" ]

end LeanFormal.IUT.Audit

#check LeanFormal.IUT.Audit.S3137R1RegistryCanonical
#check LeanFormal.IUT.Audit.S3137R1ConsumerEdges
#check LeanFormal.IUT.Audit.S3137R1GreenConsumers
