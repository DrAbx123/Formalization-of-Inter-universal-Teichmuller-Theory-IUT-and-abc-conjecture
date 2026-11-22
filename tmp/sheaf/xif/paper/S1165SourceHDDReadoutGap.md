# S1165: SourceHDDReadout exact target / first gap

Date: 2026-10-30. Exact target specification; first gap identified.
No weak Prop interface was created.

## Target object (to be built, not instantiated)

SourceHDDReadout should be a structure with actual data fields, not Prop
placeholders:

* dsc : H2FProcession I (actual);
* stage : Nat;
* localField : Fin (stage+1) -> Type, with the actual completion field/normed
  data for the stage coefficients;
* packet : Type, the actual finite log-shell tensor packet (Qp-module,
  finite-dimensional, normed);
* stageToLocal : (FStageCapsule I stage) -> localField assignment, proving each
  stage coefficient is read in the corresponding actual local field;
* localToPacket / tensorMap : the actual tensor/field-product realization map;
* hull : Set packet, the prescribed holomorphic hull;
* detData : PaperDeterminantLogVolumeData with the actual determinant line/
  normalization;
* readout : Real, the dsc -> hull+det signed readout;
* consumer : the actual source consumer of readout (not a Prop stand-in).

The target equality/inequality fields must use these actual objects; no
arbitrary Set, unit ball, or weak Prop.

## Actual donors checked

* H2FProcession.canonical with canonical_stage_strip = I.fPrimeStripAt and
  canonical_stage_link = I.fLinkAt; stage source/strip/link recovery.
* FStageCapsule/FStageInclusion actual finite stage data.
* SourceOneColumnArithmeticHolomorphicStructure (Card AS), actual finite-place
  instance actualOneColumnFinitePrimePlace for FinitePrimePlace 2 7.
* SourceArithmeticVectorBundle (Card AV) and SourceLocalizationExpressible
  (Card SL): reduced, not actual paper bundles/SHE landing.
* exists_realized_tensorLogShell_hull: actual finite field-product
  decomposition, nonzero scales, hull = region lam, compactness, unit subset,
  Haar positivity/finiteness, normalized log data.
* GlobalKummerIndActionsData: actual Kummer arrow/layer, Ind1/Ind2 local
  equivalences, Ind3 stage/action/comparison, global Theta packet.

## First gap

The first missing datum is the capsule -> local-field/tensor assignment:

  stageToLocal : FStageCapsule I stage -> actual localField
  together with the proof that the stage strip/source data correspond to the
  same actual completion K_v / O_v, and the actual map to the finite tensor
  packet.

H2FProcession only supplies stage strips/links (FPrimeStrip), not local fields,
completions, norms, or the tensor packet.  Card AS is abstract except for the
separate finite-prime-place instance; there is no theorem identifying a
capsule stage coefficient with that instance.  Consequently the hull and det
readout cannot yet be stated over the actual packet.

This is the exact first gap; no weak interface or Prop placeholder was added.

## Consumer

The intended consumer is the Step 3.11.5 / dsc -> hull+det readout feeding the
SHE special-case q vs hull comparison; it remains blocked on stageToLocal and
the tensor/hull/determinant realization.

## Audit

S1165SourceHDDReadoutGapActual.lean EXIT=0; donors typechecked; no fake.
