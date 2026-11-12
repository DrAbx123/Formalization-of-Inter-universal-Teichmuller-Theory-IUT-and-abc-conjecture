# S2143: D9 stack quotient witness — decomposition and exact first missing

Date: 2026-11-02. Status: no actual S1971StackQuotientWitness constructed. The witness is decomposed into an actual stack fiber half and a quotient universal-property half; the two forms are proved equivalent. No IsStack instance is produced or claimed.

## 1. Raw witness

S1971StackQuotientWitness l A has fields:

- cF : HyperbolicOrbicurve (S1732A l).F;
- pointwise : for every U, Nonempty (Equivalence (cF.stack.fiber.obj U) (S1971PointwiseQuotient U));
- quotient : OrbicurveSignInvariantMorphism A cF;
- witness : OrbicurveSignQuotientWitness A quotient.

The exact first missing recorded by S2104 is Nonempty (S1971StackQuotientWitness l A).

## 2. Decomposition

File: tmp/sheaf/xif/paper/S2143StackQuotientWitnessActual.lean

- S2143StackFiberData l:
    Q : EtaleStackPseudofunctor (S1732A l).F;
    isStack : Q.IsStack (etaleTopology (S1732A l).F);
    pointwise : forall U, Nonempty (Equivalence (Q.obj U) (S1971PointwiseQuotient U)).

- S2143CF l D:
    realizedHyperbolicOrbicurve (S1732A l).F D.Q D.isStack
      S1964HonestQuotientSignature S1964HonestQuotientSignature_hyperbolic.
  The honest signature is used as the normalized label; the raw witness does
  not fix a signature.

- S2143QuotientUniversalProperty l A D:
    exists quotient : OrbicurveSignInvariantMorphism A (S2143CF l D),
      Nonempty (OrbicurveSignQuotientWitness A quotient).

- S2143StackQuotientWitness l A:
    fiber : S2143StackFiberData l;
    universal : S2143QuotientUniversalProperty l A fiber.

## 3. Actual equivalence

- S2143Witness_of_S1971:
    Nonempty (S1971StackQuotientWitness l A) ->
      Nonempty (S2143StackQuotientWitness l A).
  From a raw witness W, take the actual fiber W.cF.stack.fiber and its stack
  certificate; the quotient map and universal witness are the S2104 honest
  transport of W.quotient and W.witness.

- S1971Witness_of_S2143:
    Nonempty (S2143StackQuotientWitness l A) ->
      Nonempty (S1971StackQuotientWitness l A).
  Build the raw witness with cF := S2143CF l W.fiber, pointwise := W.fiber.pointwise,
  and the quotient/universal data from W.universal.

- S2143Witness_iff: the two witness forms are equivalent.

Hence the raw S1971 first missing is exactly the decomposed pair
(S2143StackFiberFirstMissing, S2143QuotientUniversalProperty).

## 4. Exact first missing

S2143StackFiberFirstMissing l := Nonempty (S2143StackFiberData l):

  an actual etale stack fiber Q with Q.IsStack and a pointwise equivalence of
  Q.obj U with the pointwise sign action groupoid S1971PointwiseQuotient U,
  for every test object U.

S2143QuotientUniversalProperty l A D:

  a sign-invariant quotient morphism from the sign action to S2143CF l D,
  together with its bicategorical universal property
  (OrbicurveSignQuotientWitness A quotient).

Neither is constructed.  The IsStack field is part of the missing fiber datum;
this file does not prove it.

## 5. Consumers

- S2143HonestQuotient_of_witness:
    Nonempty (S2143StackQuotientWitness l A) ->
      Nonempty (S2104HonestCFQuotient l A).
- S2143S1964FirstMissing_of_witness:
    same hypothesis -> S1964FirstMissing l A.
- S2143StackFiberFirstMissing_of_witness:
    same hypothesis -> S2143StackFiberFirstMissing l.

## 6. S2103 prestack half

Unchanged. The exact first missing there is SlicePushNaturality (S2103FirstMissing K),
i.e. the compatibility of GrothendieckTopology.overMapPullbackComp with
Over.iteratedSliceEquivOverMapIso (backward form). It is independent of the
quotient universal property.

## 7. No fake

No IsStack instance is declared or claimed. No pointwise groupoid is substituted
for the stack witness; the pointwise equivalence is a field of the missing fiber
datum, not a construction. No label-only representable orbicurve is used.
Axioms: propext, Classical.choice, Quot.sound.

## Verification

- EXIT=0
- SHA256: 2cf9c5c4fee9e9512022b947c1b571ba64185348eb10f673c6c16e2b023848bd
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2143StackQuotientWitnessActual.olean, size 122984
- axioms for all seven declarations: propext, Classical.choice, Quot.sound.
