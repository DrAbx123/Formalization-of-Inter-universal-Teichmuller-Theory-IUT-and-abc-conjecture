/-!
# S3139: first-triangle residual checklist after the C3 closure (data only)

RESOLVED (with certification):
* C1 source infinite-place choice — S3139C1InfinitePlaceActual (results:148946; CITABLE; three decls).
* C2 independent missing data — reduced to M0/M1 by stage4 maps (S3139C2CoordinationResidualActual doc).
* C3 (Ind1) bridge dependency — S3139C3Ind1BridgeActual.sourceInd1BridgeDependency_Real_holds (results:149009; CITABLE).
* C3 convention identification — S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds (results:151396; CITABLE; first real residual closure).
* Galois-Kummer compatibility — S3139C2KummerArtinTheoremActual (theorem via Brauer pairing; results:148515).
* archimedean channel / integration / final composition / route composition (S3139 files, all EXIT=0+trio).

OPEN (route residual, exact names + owners):
* M0/R1 same-C identification F ~ F_mod — owner mainline R1.
* M1/R1 place selection — qpilot S3133M1ContractSeparatedMissing (S3133M1ContractObstructionActual) /
  S3133M1Remaining (S3133M1InjectionReductionActual), iff proved.
* capsule-label link Capsule j.val <-> Bad/V — contract-separated extra data (qpilot/lattice).
* stage4 canonical unit map — S3136LGPGlobalUnitsToLocalUnitsActual.lgpGlobalUnitsToLocalUnits.
* fourth-triangle arithmetic inputs — signed Theta-hull value + (xi-f) inclusion (shehdd route).

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.FirstTriangleResidualChecklistActual

/-- One open route residual with owner. -/
structure FirstTriangleOpenResidual where
  id : String
  owner : String
  exactName : String
  pageRefs : String

/-- The open first-triangle route residual list after the C3 closure. -/
def firstTriangleOpenResiduals : List FirstTriangleOpenResidual :=
  [ { id := "FT.M0.same-C", owner := "mainline R1",
      exactName := "same-C identification F ~ F_mod", pageRefs := "IUT III:604-620" },
    { id := "FT.M1.place-selection", owner := "qpilot",
      exactName := "S3133M1ContractSeparatedMissing / S3133M1Remaining",
      pageRefs := "IUT III:604-620; Fig I.4-I.6" },
    { id := "FT.M1.capsule-label-link", owner := "qpilot/lattice (contract-separated)",
      exactName := "Capsule j.val <-> Bad / V link",
      pageRefs := "SourceProcessionCapsuleOriginalInput docstring" },
    { id := "FT.stage4.unit-map", owner := "stage4",
      exactName := "lgpGlobalUnitsToLocalUnits (S3136LGPGlobalUnitsToLocalUnitsActual)",
      pageRefs := "IUT III:616-620, Fig I.5" } ]

/-- The resolved first-triangle items with their evidence lines. -/
def firstTriangleResolvedItems : List (String × String) :=
  [ ("C1.infinite-place-choice", "S3139C1InfinitePlaceActual results:148946"),
    ("C2.independent-data", "reduced to M0/M1 (S3139C2CoordinationResidualActual)"),
    ("C3.ind1-bridge-dependency", "sourceInd1BridgeDependency_Real_holds results:149009"),
    ("C3.convention-identification", "sourceInd1ConventionIdentification_holds results:151396 (first real closure)"),
    ("C2.galois-kummer-compat", "S3139C2KummerArtinTheoremActual theorem results:148515"),
    ("route.composition", "S3139FirstTriangleRouteCompositionActual.firstTriangleRouteComposition") ]

end LeanFormal.IUT.XiFPaper.FirstTriangleResidualChecklistActual
