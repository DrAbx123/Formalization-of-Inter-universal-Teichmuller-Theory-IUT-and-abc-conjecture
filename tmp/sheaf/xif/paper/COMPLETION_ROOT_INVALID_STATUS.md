# Completion-root dependency status: INVALID

Date: 2026-10-29. Supersedes earlier "missing completion root" statements.

## Ground truth

S342 proves, using SourceDefinition31D4TateQIdentification:

* any QParameterTwoLRootCard for qVFamily forces l | order(qVFamily), while
  the actual SourceTateComparisonWitness supplies Coprime(order(qVFamily), l);
* therefore:

  qVFamilyTwoLRootCard_impossible :
    not Nonempty (QVFamilyTwoLRootCard T b)

  missingKummerHenselInput_impossible :
    not MissingKummerHenselInput T b

  twoLthRootData_impossible :
    not Nonempty (TwoLthRootData T b)

  natRootSystem_impossible :
    not Nonempty (NatRootSystem (qVUnit T b))

The completion 2l-th-root object is not "missing Kummer/Hensel"; it is FALSE
for the actual qVFamily.  Kummer surjectivity cannot change the order.

## INVALID as paper objects / actual results

All declarations whose type is a completion root card/system/data, and all
conditional constructions taking such a datum, are INVALID as paper results.
The implications remain formally true only because their premise is false.

### PaperCompletionThetaValueActual.lean
INVALID:
* PaperQRootCard
* paperQRoot, paperQRoot_pow, paperQRoot_ne_zero
* paperCompletionThetaValue, paperCompletionThetaValue_pow_twoL,
  paperCompletionThetaValue_ne_zero
* paperCompletionThetaImageSet, paperCompletionThetaValue_mem_image
* PaperQRootCardGap

### S325CompletionThetaMuOrbitActual.lean
INVALID (all take R : PaperQRootCard):
* muCompletionFactor, muCompletionAction
* paperCompletionThetaMuValue, paperCompletionThetaMuValue_pow_twoL
* muCompletionAction_muCompletionAction
* paperCompletionThetaMuOrbit, paperCompletionThetaMuImageUnion
* paperCompletionThetaValue_mem_muImageUnion

### S343CompletionThetaC3TensorActual.lean
INVALID as paper theta image:
* c3ThetaTensorImagePoint, c3ThetaMuImagePoint
* c3ThetaMuOrbit, c3ThetaMuImageUnion
* c3MuTensor/c3MuAction are only an abstract diagonal mu action, not a paper
  root image; do not use them to claim the paper Theta side.

### S330QVFamilyRootCardActual.lean
INVALID:
* QVFamilyTwoLRootCard (type has no inhabitant)
* QVFamilyTwoLRootCardGap (false)
* MissingKummerHenselInput (false)
* qVUnitRootOfCard, qVUnitRootOfCard_pow
* twoLthRootDataOfCard, twoLthRootData_nonempty_of_card

### S319CompletionRootFromTorsion23Actual.lean
INVALID status: records the gap as "missing"; it is impossible.
* MissingCompletionRootFromTorsion23
* twoLthRootData_of_missingCompletionRoot
* completionQVUnit (only the qVUnit spelling is actual, not a root)
* twoLRootExistenceGap_iff_missing
* MissingCompletionRootFromTorsion23Required

### TwoLthRootQVActual.lean
INVALID as actual root data:
* TwoLRootExistenceGap (false, not merely a gap)
* TwoLthRootData (no inhabitant)
* twoLthRoot, twoLthRoot_pow, twoLthRoot_completion_pow
* twoLthRoot_ratio_mem_mu, twoLthRoot_ambiguity
* twoLthRootDataOfRootSystem, twoLthRootData_exists_of_rootSystem
Valid pieces retained: qVUnit, qVUnit_apply, muTwoLRoots, twoLExponent.

### BadPlaceHalfRootSupplyActual.lean
INVALID as actual root supply:
* HalfRootInCompletion
* every construction from HalfRootInCompletion
* HalfRootCompletionGap (false, not missing)
Valid: no counterexample is invalidated; BadPlaceHalfRootCriterionActual's
padic_five_no_twoL_root remains valid evidence.

### CompletionBlockThetaImageActual.lean
INVALID as actual completion theta image (conditional on HalfRootInCompletion):
* completionThetaValue, completionThetaMuValue
* completionThetaImagePoint, completionThetaImageUnion
* completionSingleLambda, completionThetaScaledPoint,
  completionThetaScaledHull
* completionThetaHullMeasure, completionThetaHullLog

### S310CompletionSameCarrierPairActual.lean
INVALID as paper same-carrier pair:
* CompletionRootDataFamily
* CompletionRootSystemExistenceGap
* CompletionRootSystemExistenceGap_iff
* ThetaCompletionHullGap / CompletionSameCarrierPair and instances
  conditional on root data
Valid: qPilotCompletionImagePoint/completionQVFamProductPoint are q-side
spellings, not root constructions.

### S313CompletionThetaSideObjectActual.lean
INVALID as completion Theta side object:
* completionThetaRoot, completionThetaImage, completionThetaImageSet
* completionThetaReference (only a ball, not paper hull)
* completionThetaScaledRegion, completionThetaHull
* completionThetaHullMeasure, completionThetaHullLog
* CompletionThetaSideObject, completionThetaSideObject
* CompletionThetaRootSourceGap (false)

### LGP / algebraic-closure root branch (also non-paper carrier)
These do not use completion roots, but they use AlgebraicClosure roots, which
are also not the paper O^tri/root-stack carrier.  Keep AUX, not paper:
* LGPPhiInputActual.lgpTwoLthRoot, lgpThetaValue, LGPThetaRootSystemGap
* LGPThetaActionActual.lgpThetaValue and action data
* QVSameSourceThetaImageActual.qVThetaImageVector / qVThetaImageSet
* TwoLthRootKummerActual.hodgeTwoLthRoot and descendants
* LGPPhiInputFromAlgebraicClosureActual / LGPPhiInputConstructionActual
  algebraic-closure root normalization data

### Already-surrogate, not paper
* S317QPilotThetaSameCompletionBlockActual: coefficientSurrogateImageSet/Hull
  (order/(2l) coefficient, not root value) — do not use.
* CompletionValuedThetaHullMuLogActual: paperRootCoefficient... uses the
  normalized coefficient hull, not the root-valued paper hull.
* S346OrbifoldStructuralSheafActual: exact spec only; no carrier inhabitant.
  This is the currently correct route, not a completion root.

## Correct route status

The paper carrier must be the O^tri(T_x)/O^triangleright root-stack carrier.
S346 records the minimal exact spec and has no inhabitant.  Until an actual
O^tri carrier and q_v^(1/2l) section are supplied, no paper Theta value/object
may be built from a completion root.

No L/transport/normalization substitution is valid either.

## Documentation statuses needing correction

* ROOT_EXISTENCE_GAP.md: "missing" should be read as "completion-card
  impossible; O^tri carrier missing".
* OBJECT_ALIGNMENT_AUDIT.md root entry: same correction.
* Any target-strength ledger line using twoLthRoot/PaperCompletionThetaValue:
  INVALID as paper dependency.
