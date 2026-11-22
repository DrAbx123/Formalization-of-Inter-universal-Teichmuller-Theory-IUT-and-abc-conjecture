# C7-a stage 1: theta-image containment donor

Node: C7-a (child of C7)
Parent: C7 SourceHolomorphicHull
Stage: 1 (statement/route only; no Lean file, no compile)
Date: 2026-10-23
Owner: kummer
Consumers: C7 image_subset_hull, C7 contains_permitted

## Exact target statement

For the actual C3 tensor tuple and an explicit T11 interface

    T : SourceThetaIQInterface (I := I) C3

and procession n, the actual theta image family is contained in the actual
canonical hull:

    theorem c7_theta_image_subset_canonicalHull
        (T : SourceThetaIQInterface (I := I) C3)
        (n : ThetaPilotCarrier l) :
        SourceThetaToIQ.image (I := I) C3 T n subset
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

Pointwise form used by the C7 field:

    theorem c7_thetaImage_mem_canonicalHull
        (T : SourceThetaIQInterface (I := I) C3)
        (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
        T.thetaImage n j in
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

Exact T11 reduction:

    T.thetaImage n j = C3.tensorLanding (T.thetaCompletion n j)
      -- SourceThetaIQInterface.thetaImage_eq

## Allowed input

- C3 : SourcePilotRegionData I.
- T11 interface T with thetaCompletion, thetaScale, thetaImage, thetaImage_eq.
- C6ActualIQData.actual carrier C6IQCarrier C3.tensorPlaces C3.tensorTuple.
- production donors: arithmeticTupleCanonicalHull,
  arithmeticTupleHullPullback/arithmeticTensorProductImage,
  C3.tensorLanding and C3.tensorLanding_q.

## Why current T11 is insufficient

SourceThetaIQInterface.thetaCompletion is an arbitrary function
ThetaPilotCarrier -> SignedLabel -> CommonPrimeCompletion. T11 records it as
the missing actual theta map. It has no field saying that thetaCompletion n j
lies in the tensor/integral unit region whose image is the canonical hull.
Thus canonical-hull containment cannot follow from the current interface; a new
source field/lemma is required, not just a proof step.

## Required donor / bridge (exact gap)

At least one of:

1. A T11 source field
     thetaCompletion_mem_unitRegion :
       forall n j, C3.tensorLanding (T.thetaCompletion n j) in
         arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple
   plus a canonical-hull/unit-reference scaling theorem producing containment in
   arithmeticTupleCanonicalHull; or
2. A direct source theorem
     thetaImage_mem_canonicalHull :
       forall n j, T.thetaImage n j in
         arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple.

Option 1 is preferred: the paper theta image is a local theta/integral unit
image, and the canonical unit reference is the actual lambda-O region.

## Proof route once donor exists

1. Rewrite T.thetaImage n j via T.thetaImage_eq to C3.tensorLanding
   (T.thetaCompletion n j).
2. Apply the new thetaCompletion_mem_unitRegion field.
3. Use the canonical unit-reference inclusion/scaling theorem
   (arithmeticTupleCanonicalUnitReference_subset... / canonical hull region
   decomposition) to land in arithmeticTupleCanonicalHull.
4. Extend pointwise membership to SourceThetaToIQ.image by rintro j rfl.

## Acceptance

- statement_compiles for C7-a statement;
- proof_body_checked once donor field is added to T11 (or separate source
  theta-unit theorem is proved);
- no arbitrary membership field, no True/PUnit, no free image set.

## Forbidden substitutions

- Do not assume T.thetaImage membership as a free C7 field.
- Do not replace thetaCompletion by C3.qUnit powers (T11 forbids this).
- Do not use the value-monoid SourceImageHull as a proxy for the IQ hull.
