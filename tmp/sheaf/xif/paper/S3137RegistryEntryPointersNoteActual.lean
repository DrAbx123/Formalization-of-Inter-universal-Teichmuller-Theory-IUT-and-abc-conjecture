import LeanFormal.IUT.Audit.Status

/-! # S3137: registry/Part entry pointers — exact file + declaration names

For the next single reopen, the Part/registry notes should point at these exact
declarations (all EXIT0 + checker CITABLE unless noted).  Registry frozen 14041 (third combined reopen: Option-B model-route closure);
mainline applies the narrow note edit; shehdd re-pins.

M2a (CLOSED): S3133M2aClosedActual.S3133RationalFiveQCompletion_valuation/_ne_zero/
_norm, S3133RationalFiveCompletionNorm_holds, S3133GaussianCanonicalQNorm_holds;
S3133M2aNormReductionActual.S3133RationalFiveCompletionNorm; bridge Mathlib
valuedAdicCompletion_eq_valuation'; lattice S3137M2aToolActual.

M2b/R1 final interface: S3133GaussianModelMapResidualFinalActual:
S3133GaussianModelMapResidualFinal (only m1_indexInjection + m2b_clauseB),
S3133GaussianModelMapRemainingFinal, m0/m3 proved, of_minimal,
S3133GaussianQParameterMatchAtBase_iff_clauseB, S3137R1_interface_final;
R1 = M1 + M2b.

Model components (qpilot, CITABLE): S3133ModelVBasisActual (S3135ModelPlace,
S3135ModelV, vFive, vInf, vFive_ne_vInf); S3133ModelFPrimeStripActual
(modelFPrimeStrip); S3133ModelHodgeTheaterActual (modelHodgeTheater,
modelHodgeTheater_arithmetic, modelHodgeTheater_thetaPacket).
Model skeleton (lattice, CITABLE): S3137ModelIndexArithmeticActual,
S3137ModelTheaterSkeletonActual, S3137ModelPlaceToModActual,
S3137ModelPlaceToModConstructionActual (modelPlaceToModDataOfDistinct vFive vInf
vFive_ne_vInf wired in S3137ModelPlaceToModWiringActual),
S3137ModelOriginalInputSkeletonActual (modelOriginalInputOfSkeleton),
S3137ModelHodgeTheaterObstructionActual.
-/

namespace LeanFormal.IUT.Audit

/-- Data: exact declaration pointers for the next reopen. -/
def S3137RegistryEntryPointers : List (String × String) :=
  [ ("INDEX.R1.M2.base-q-transport", "S3133M2aClosedActual.S3133RationalFiveQCompletion_valuation/_ne_zero/_norm + S3133RationalFiveCompletionNorm_holds + S3133GaussianCanonicalQNorm_holds (CITABLE 6 decls); S3133M2aNormReductionActual.S3133RationalFiveCompletionNorm (CITABLE 2 decls)"),
    ("INDEX.R1.final-residual-interface", "S3133GaussianModelMapResidualFinalActual: S3133GaussianModelMapResidualFinal (m1_indexInjection + m2b_clauseB), S3133GaussianModelMapRemainingFinal, m0/m3 proved, of_minimal, S3133GaussianQParameterMatchAtBase_iff_clauseB, S3137R1_interface_final"),
    ("INDEX.MODEL.from-scratch-theater-family", "S3133ModelHodgeTheaterActual.modelHodgeTheater (fiber value) + S3137ModelTheaterSkeletonActual.ModelTheaterData/toFamily + S3137ModelHodgeTheaterObstructionActual.no_constant_modelHodgeTheater_family (obstruction)"),
    ("INDEX.MODEL.from-scratch-original-input", "S3137ModelOriginalInputSkeletonActual.modelOriginalInputOfSkeleton (parameterized hInj/hAlign)"),
    ("INDEX.MODEL.place-to-mod-literal", "S3137ModelPlaceToModWiringActual.modelPlaceToModDataS3135 + _faithful (wired to S3133ModelVBasisActual.vFive/vInf/vFive_ne_vInf)"),
    ("INDEX.MODEL.from-scratch-index-arithmetic", "S3137ModelIndexArithmeticActual.modelIndexEquiv/modelPermutation") ]

/-- INDEX note: registry entry pointers. -/
def S3137RegistryEntryPointersRecord : Obligation :=
  { id := "S3137.index.registry-entry-pointers"
    source := "S3133M2aClosedActual; S3133GaussianModelMapResidualFinalActual; S3133ModelVBasisActual/FPrimeStrip/HodgeTheater; S3137 model skeleton files"
    status := VerificationStatus.interface
    note := "EXACT DECLARATION POINTERS for the single next reopen (registry frozen 14041 (third combined reopen: Option-B model-route closure); mainline narrow note edit; shehdd re-pin): M2a closed decls; R1 final interface (R1 = M1 + M2b); model components + model skeleton + constant-theater obstruction + literal placeToMod wiring. Data only."
    dependsOn := ["S3137RegistryEntryPointers"] }

end LeanFormal.IUT.Audit