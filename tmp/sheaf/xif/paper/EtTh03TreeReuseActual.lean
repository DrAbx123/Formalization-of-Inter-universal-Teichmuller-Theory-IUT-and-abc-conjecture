/-!
# EtTh03: tree-asset reuse map for [EtTh] (data only; external-object target)

Tree assets to REUSE for the étale-theta-function external object (no re-proof):
* theta packet / initial Theta data -> LeanFormal.IUT.Theorem311Source.SourceDefinition31Data
  (SourceDefinition31Boundary.lean:667) and the theta packet fields (theaterAt n m).
* theta quotient level (A-class, already proved):
  LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean:1 thetaDerivedSubgroup,
  :4 thetaCommutatorKernel, ThetaQuotient, EllipticAbelianization,
  thetaCommutatorKernel_le_derivedSubgroup, thetaToElliptic (+_mk, _surjective),
  thetaPowerKernel, ellipticPowerKernel, ModLThetaQuotient, modLThetaProjection
  (+_surjective), thetaToElliptic_maps_powerKernel, modLThetaToElliptic (+_surjective).
* concrete source étale theta bridge: LeanFormal/IUT/IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean:44
  sourceModel := ConcreteSourceFrobenioidBridge.concreteStageModel; the concrete
  Gaussian packet prime data (packet_rationalPrime_eq_five) already used by qpilot.
* Frobenioid side: LeanFormal/IUT/IUTII/Frobenioid/ConcreteSourceFrobenioidBridge.lean
  ConcreteSourceFrobenioidBoundary (structure) + concreteSourceFrobenioidBoundary:? : 
  noncomputable def concreteSourceFrobenioidBoundary (l) and boundary_cStage /
  boundary_place / boundary_model / boundary_model_input / boundary_kernel,
  concrete_place_* (comap/stable/multiplicative/selected_input/input_arithmetic),
  source_stage_base_connected; concreteStageModel : Iut.FrobenioidPresentation.
* Iut foundations (importable, 205 oleans): Iut.Foundations.SourceModelFrobenioidPresentation
  (frobenioidPresentation [IsConnected D]), SourceModelFrobenioidRationalNaturality,
  SourceModelFrobenioidZeroEvaluation.
* Frobenioid examples/actions (production tree): LeanFormal/IUT/IUTII/Frobenioid/
  DivisorialMonoidMinimalReplacement.lean, Example36FrobeniusValueAction.lean,
  Example36PrimeStripDivisorFrobenius.lean, Example36LogShellFrobeniusAction.lean,
  Example36FrobenioidTransport.lean, Example36Frobenioid... (many Example36 assets).
* route/A35/GenEll consumers (this stream, citable): S3139C3ConventionClosureActual
  (full-poly-iso counterpart), Indet01-03 (A35 Ind1,2,3 statement layer),
  GenEll09/10/11 (H6 interface-level closed; P3 IV section2 consumer).
* canonical rooted Q_C/H_C: S3132CanonicalRootedHC/CG files (S3131CanonicalRootedQC_le_HC
  green fourth-triangle inequality; S3132RootedScaling* for sharp R2 residual).
Honest: corpus [EtTh] text present (papers/motizuki_corpus/text/The Etale Theta
Function and its Frobenioid-theoretic Manifestations.txt + comments/related
expositions).  Deep theta results remain class-B D-inputs (EtTh02DeepInputsActual,
proved := false).
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtTh03TreeReuseActual

/-- Reuse rows for [EtTh]: (paper object, tree asset, class). -/
def etThTreeReuse : List (String × String × String) :=
  [ ("theta packet / initial Theta data", "SourceDefinition31Data (SourceDefinition31Boundary.lean:667) + thetaPacket", "A (reuse)"),
    ("theta quotient / theta group", "EtaleThetaQuotient.lean: thetaDerivedSubgroup/thetaCommutatorKernel/ThetaQuotient/EllipticAbelianization + surjectivity theorems", "A (reuse; proved)"),
    ("mod-l theta quotient", "EtaleThetaQuotient.lean: ModLThetaQuotient/modLThetaProjection(+_surjective)/modLThetaToElliptic(+_surjective)", "A (reuse; proved)"),
    ("concrete Gaussian theta bridge", "ConcreteSourceEtaleThetaBridge.lean:44 sourceModel := concreteStageModel; packet_rationalPrime_eq_five", "A (reuse)"),
    ("tempered Frobenioid manifestation", "ConcreteSourceFrobenioidBridge.lean: ConcreteSourceFrobenioidBoundary + concreteSourceFrobenioidBoundary(l) + boundary_theorems; concreteStageModel : Iut.FrobenioidPresentation", "A (reuse)"),
    ("model Frobenioid / divisor theory", "Iut.Foundations.SourceModelFrobenioidPresentation.frobenioidPresentation; DivisorialMonoidMinimalReplacement; Example36FrobeniusValueAction etc.", "A/B (reuse; paper clauses class B)"),
    ("Frobenioid-theoretic manifestation (§3/§5)", "ConcreteSourceFrobenioidBridge boundary + tree Frobenioid objects", "A (construction) / B (paper semantics)"),
    ("full poly-isomorphism / 0-column", "S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds", "A (certified closure)"),
    ("Ind1,2,3 indeterminacy (A35)", "Indet01FirstTriangleIndActual / Indet02BPSMultiradialUpToActual / Indet03A35MappingActual", "statement layer; Audit Ind1/2/3 PENDING"),
    ("H6 GenEll transfer", "GenEll10H6ClosureActual (interface-level closed)", "interface-level A; deep GenEll inputs class B") ]

end LeanFormal.IUT.XiFPaper.EtTh03TreeReuseActual
