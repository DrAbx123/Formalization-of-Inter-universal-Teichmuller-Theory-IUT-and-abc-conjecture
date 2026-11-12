# FINITE-DIM-VOLUME-PLAN — replacing arbitrary FinalL measures by a finite block

Status: READ-ONLY plan, 2026-11-12. No compile.
Problem: FinalL = AlgebraicClosure is not locally compact / not finite-dimensional
over Qp, so FinalLValuedCarrier has no actual Haar measure. The arbitrary
measure in S956/S962/S971/S979/S981 is therefore a model defect, not a removable
simplification. We check whether the S971 regions can be pulled back to a finite
ArithmeticTensorTupleBlock.

## 1. Two finite blocks

C3LogShellTensorBlockL (Mzk1C3LogShellTensorLActual.lean:43-45):
  abbrev C3LogShellTensorBlockL : Type :=
    ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple.
  C3LogShellPlaceL i : FinitePlaceAtPrime I.initial.arithmetic.Fmod C3L.p.
  It has actualC3LogShellTensorHaar, actualC3LogShellTensorRegion,
  compactness and the S1391/S2807 log-volume interface.

qVFamTensorBlock (QVFamTensorCoefficientActual.lean:72-73):
  abbrev qVFamTensorBlock : Type :=
    ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple.
  qVFamTensorPlaces : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b),
  one-factor tuple Unit.

Both are definitions of the same general ArithmeticTensorTupleBlock family, but
with different place/tuple data:
- base field: I.initial.arithmetic.Fmod vs T.arithmetic.F;
- prime: C3L.p vs qVFamTensorP T b;
- index/tuple: C3L.tensorIndex/tensorTuple vs Unit/qVFamTensorTuple;
- measure: actualC3LogShellTensorHaar vs no actual Haar on the qVFam block (only
  the general finite-dimensional addHaar available).
No equality or equivalence between the two blocks is present. Exact
identification conditions are listed in section 5.

## 2. S971 definitions and pullback

S971 (S971TensorRegionImageActual.lean):
  tensorThetaRegionImage :=
    qVFamToLValued '' paperRootThetaImageNZ;
  tensorThetaRegionIndUnion :=
    tensorThetaRegionImage ∪ thetaImageIndUnion;
  tensorRegionHull D := closure (tensorThetaRegionIndUnion) under D.topologicalSpace;
  qPilotPaperImage_subset_tensorRegionHull :
    qPilotPaperImageInLValued ⊆ tensorRegionHull D.

qVFamToLValued (PaperFinalLValuedTensorCarrierActual.lean:48-50):
  qVFamToLValued x := TensorProduct.tmul Qp x (1 : FinalL T b).
S945 qPilotPaperImageInLValued :=
  qVFamToLValued '' qPilotPaperRegion.

So for qPilotPaperImage and tensorThetaRegionImage there is an immediate finite
pullback: the finite regions are exactly qPilotPaperRegion and
paperRootThetaImageNZ inside qVFamTensorBlock. No inverse map is needed.

But tensorThetaRegionIndUnion also contains thetaImageIndUnion
(PaperFinalLValuedThetaIndHullActual.lean:42-48):
  rootThetaImageInLValued ∪ ind1Image ∪
    Union_{u : (FinalL T b)^x} ind2Image u ∪
    Union_{u,m} ind3Image u m.
The Ind2/Ind3 unions quantify over ALL units of FinalL, not over units of the
finite qVFam block. Multiplication by such a unit changes the L tensor factor;
the resulting point is not necessarily in the image of qVFamToLValued, and
there is no finite region whose image is ind2Image u. Therefore:

- PULLBACK POSSIBLE for qPilotPaperImage and tensorThetaRegionImage;
- PULLBACK NOT POSSIBLE for the full thetaImageIndUnion/tensorRegionHull as
  currently defined, because of the all-FinalL-unit Ind2/Ind3 orbits.

A finite replacement must either:
  (a) restrict Ind2/Ind3 to units coming from the finite qVFam block (different
      object; needs an explicit finite Ind action), or
  (b) omit the arbitrary L-unit orbit and retain only the finite qVFam image
      (a weaker hull; not S971).
Do not identify the restricted object with S971 without a proof.

## 3. Finite-dimensional Haar plan

Preferred finite block for actual Haar: C3LogShellTensorBlockL, because
actualC3LogShellTensorHaar is already constructed and normalized. Plan:

1. Define finite regions in C3 block:
   qPilotRegionL : Set (C3LogShellTensorBlockL C3L),
   thetaImageRegionL : Set (C3LogShellTensorBlockL C3L),
   thetaHullRegionL : Set (C3LogShellTensorBlockL C3L).
   Use existing actualC3LogShellTensorRegion for the theta side; the qPilot
   region must be constructed or transported from qPilotPaperRegion.
2. Prove inclusion qPilotRegionL ⊆ thetaHullRegionL in the finite block
   (the finite analogue of S971:61).
3. Use actualC3LogShellTensorHaar and haarLogVolume_mono to get
   haarLogVolume mu qPilotRegionL <= haarLogVolume mu thetaHullRegionL.
4. Add positivity/finiteness (compact region; actual Haar finite on compact);
   the S971/S979 proof already separates hpos/hfin.
5. If needed, use the finite qVFamTensorBlock with Measure.addHaar (finite
   dimensional Qp vector space) and a finite topology; this is a second finite
   model, not the C3L Haar unless the blocks are identified.

Objects needed:
- finite-dimensional instance for ArithmeticTensorTupleBlock (exists);
- Haar measure on the finite block: actualC3LogShellTensorHaar for C3L;
  Measure.addHaar for an arbitrary finite-dimensional Qp vector space;
- measurable/Borel instances (already in C3L);
- qPilot/theta regions and inclusion;
- positivity/finiteness of the Haar masses.

## 4. What the finite volume inequality would be

On the C3 block:
  mu := actualC3LogShellTensorHaar C3;
  qRegion, thetaRegion : Set (C3LogShellTensorBlockL C3L);
  qRegion ⊆ thetaRegion;
  haarLogVolume mu qRegion <= haarLogVolume mu thetaRegion.
This is a genuine finite-dimensional volume comparison. It can feed the
C3/S2807 theta side (S2807_thetaHullVolume_eq_haarRegion) once qRegion is
identified with the qPilot region.

On the qVFam block:
  mu := Measure.addHaar;
  qVFamRegion := qPilotPaperRegion (finite);
  thetaVFamRegion := paperRootThetaImageNZ (finite);
  inclusion qVFamRegion ⊆ thetaVFamRegion;
  addHaar log-volume comparison.
This is a finite one-factor model; it is not the C3 multi-place determinant
unless the place data are identified.

Neither finite model by itself gives the full S971 tensorRegionHull because of
the all-FinalL-unit Ind orbits.

## 5. Exact identification conditions for C3L vs qVFam blocks

To transport a finite volume statement from qVFamTensorBlock to
C3LogShellTensorBlockL, one needs:
1. base field: T.arithmetic.F = I.initial.arithmetic.Fmod (or an explicit
   arithmetic-record equality);
2. prime: qVFamTensorP T b = C3L.p;
3. tensor index: Unit / qVFamTensorV equivalent to C3L.tensorIndex (probably
   C3L is multi-factor while qVFam is one-factor; a genuine equivalence or a
   selected factor must be supplied);
4. place: qVFamTensorPlace T b, or its Fmod restriction, equals the C3 place
   used by C3L.tensorPlaces;
5. Haar compatibility: the transported Haar equals actualC3LogShellTensorHaar
   (or differs by a known constant);
6. region compatibility: transported qPilot/theta regions equal the C3 regions;
7. unit/Ind action compatibility if the Ind orbits are included.

Current status of 1-7: not available. T.arithmetic and I.initial.arithmetic are
independent; qVFam is one-factor over F, C3L is multi-factor over Fmod; no place
equality or tensor-index equivalence is proved. This is the same carrier GAP
as in A1070 and A1126.

## 6. Verdict

- C3LogShellTensorBlockL and qVFamTensorBlock are the same ArithmeticTensorTupleBlock
  family but different data; no identification theorem exists.
- qPilotPaperImage and tensorThetaRegionImage can be pulled back to finite
  qVFam regions by definition (they are images under qVFamToLValued);
  tensorRegionHull/thetaImageIndUnion cannot, because they quantify over all
  FinalL units and are not in the tmul image.
- A finite-dimensional Haar/volume plan is feasible on C3L (actual Haar exists)
  or on qVFam (addHaar exists), but it is a finite replacement model, not the
  full S971 L-valued hull.
- Exact C3L <-> qVFam transport requires base field, prime, tensor index, place,
  Haar and region identifications; none are currently proved.
- The arbitrary measure fields in S956/S962/S971/S979/S981 should be marked as
  model defects on the infinite carrier, not as removable simplifications.

No Lean file written; no compile claimed.