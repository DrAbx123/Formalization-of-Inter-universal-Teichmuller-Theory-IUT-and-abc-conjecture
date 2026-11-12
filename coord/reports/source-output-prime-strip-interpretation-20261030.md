# SourceOutputPrimeStripInterpretation — exact-boundary verification

Date: 2026-10-30
Package: coord/reports/source-compute-integration-20261030.md §2, first joint.

## Correction

The previous report claimed actual constructions
(sourceEvaluationInputStrip/OutputStrip/sourceFamilyLinkAt,
SourceEnvColumnArrows/upperEnv/envSquareCommutes, forgetSourceRun).
That claim is WRONG for the current target file.

Target and mirror are byte-identical and contain only documentation + #check:

- target: LeanFormal/IUT/IUTIII/Theorem311/Output/SourceOutputPrimeStripInterpretation.lean
- mirror: tmp/sheaf/xif/paper/SourceOutputPrimeStripInterpretationMirror.lean

Evidence:
- target lines = 65; mirror lines = 65;
- SHA256 target = mirror =
  D78E66B4B59B8E2069F5707DE25FDBBB3E2E3BB08F215F4E9729407D939AE5B7;
- target declaration count for def/structure/abbrev/theorem = 0;
- target #check count = 5.

Line ranges of the target:
- 1-3: imports;
- 5-49: documentation of the exact first gap;
- 51-63: namespace plus five #check lines:
  57 #check SourceFTimesMuPrimeStrip
  58 #check SourceFTimesMuPrimeStripRem3102Diagram
  59 #check SourceFTimesMuPrimeStripRem3102Diagram.iplLink
  60 #check SourceMultiradialPresentationWiring.sourceAlgorithmOfCarrier
  61 #check IUT.Audit.iplAlgorithmicProvenanceCard.

There is no SourceEvaluationInputStrip/OutputStrip, no sourceFamilyLinkAt, no
SourceEnvColumnArrows, no upperEnv/lowerEnv, no envSquareCommutes, and no
forgetSourceRun in the target file. The previous report is superseded by this
verification.

Compile of the current exact-boundary target: EXIT=0 (only #check output).

## Actual/exact status

Actual today (in tree, not constructed in this package):
- SourceFTimesMuPrimeStripRem3102Diagram with arrow slots and commEnv
  (SourceFTimesMuPrimeStripPolyIsomorphism.lean:805-833);
- iplLink (same file:845-849);
- reduced run/output and sourceAlgorithmOfCarrier
  (ParametricCarrier.lean:403-459; SourceMultiradialPresentationWiring.lean:241);
- named consumer iplAlgorithmicProvenanceCard
  (SourceMultiradialIplLinkWiring.lean:190).

Exact first gap (unchanged): no correspondence between the algorithm
Choice/output type and FPrimeStrip V / SourceFTimesMuPrimeStrip V, and no
source-level evaluation strip construction. Therefore:
- no actual evaluation input/output strip pair;
- no actual upperEnv arrow;
- no actual adjacent Kummer square proof;
- no actual forget relation from a SourceRun to reduced output.

Accepted exit for this package is only the exact-boundary statement, not an
actual construction. No weak compatible/isActual Prop, Nonempty gate, True/PUnit,
Classical choice or arbitrary strip map is introduced.

## Actual first step (added after exact-boundary verification)

For arbitrary I : OriginalInput l V, the actual strip map on Choice = I.family.index is now implemented in the target:

- line 146: noncomputable def stripOfChoice (i : I.family.index) : FPrimeStrip V :=
    I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2;
- lines 150-152: stripOfChoice_apply (rfl);
- lines 155-157: stripOfChoice_exists;
- line 163: def SourceFamilyChoice : Type ui := I.family.index.

This is actual, for every OriginalInput I; no concrete SourceDefinition31Data/OriginalInput is constructed.
Compile target and mirror: EXIT=0.
Target/mirror after sync: 167 lines each, SHA256
DFB8086A0AE4E2D95031E1BB7991ED564323247F0DB6DBC6759290E8AE518CF6.

Next exact step (not claimed): build SourceRun / evaluation operation on
Choice = I.family.index using I.fLinkAt, then the upperEnv/Kummer square and
reduced forget relation. No such operation is asserted yet.