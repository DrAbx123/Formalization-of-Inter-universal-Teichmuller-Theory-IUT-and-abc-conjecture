# S2104: D9 honest quotient witness — exact type, consumers, conditional actual construction

Date: 2026-11-02. Status: the honest-labelled quotient is constructed from an actual S1971 stack quotient witness; the stack witness itself remains missing. No IsStack or effective-descent claim.

## 1. Exact type

S1964HonestCFQuotient l A is an abbreviation:

  S1964HonestCFQuotient l A
    = S1964CFQuotientAt l A
        S1964HonestQuotientSignature
        S1964HonestQuotientSignature_hyperbolic

Fields:
- cF : HyperbolicOrbicurve (S1732A l).F
- cF_signature : cF.signature = S1964HonestQuotientSignature
- quotient : OrbicurveSignInvariantMorphism A cF
- quotientWitness : OrbicurveSignQuotientWitness A quotient

The honest signature is (0; [2,2,2]; 1), not the paper (1,1)^pm label.

## 2. Existing consumers

- S1964FirstMissing_ofHonest : Nonempty (S1964HonestCFQuotient l A) -> S1964FirstMissing l A.
- S1983FirstMissing_iff_honest : S1983FirstMissing l A <-> Nonempty (S1964HonestCFQuotient l A).
- S1983 CFQuotientAt congr: Nonempty (S1983EtThCF l A) <-> Nonempty (S1964HonestCFQuotient l A).
- S1991HonestTargetAliasesActual: S1991HonestCFQuotientAt l A = S1964HonestCFQuotient l A (rfl).
- S2093LargeCFDataExact / S2093LargeCFFirstMissingExact consume the honest quotient as one conjunct.
- S2093LargeCFDataExact.toS1964 : S2093LargeCFDataExact l A -> S1964QuotientStructure l A.

No consumer constructs an inhabitant.

## 3. Actual conditional construction

File: tmp/sheaf/xif/paper/S2104D9HonestQuotientActual.lean

Given W : S1971StackQuotientWitness l A:

- S2104CFOfStackWitness W:
    realizedHyperbolicOrbicurve S1726K W.cF.stack.fiber W.cF.stack.isStack
      S1964HonestQuotientSignature S1964HonestQuotientSignature_hyperbolic.
  This keeps the witness stack fiber and inserts the honest signature certificate.

- S2104QuotientOfStackWitness W:
    OrbicurveSignInvariantMorphism A (S2104CFOfStackWitness W),
  with map, invariant and cocycle copied from W.quotient.  Hom of hyperbolic
  orbicurves only depends on stack.Hom (hence on the stack fiber), so the
  honest relabelling of the signature does not require a new quotient map.

- S2104WitnessOfStackWitness W:
    OrbicurveSignQuotientWitness A (S2104QuotientOfStackWitness W),
  copying descend, factor, descendTwoCell, descendTwoCell_factor and twoCell_ext.

- S2104HonestCFQuotientOfStackWitness W : S1964HonestCFQuotient l A,
  with cF_signature := rfl.

- S2104HonestCFQuotient_of_stackWitness:
    Nonempty (S1971StackQuotientWitness l A) ->
      Nonempty (S1964HonestCFQuotient l A).
- S2104S1964FirstMissing_of_stackWitness: same hypothesis -> S1964FirstMissing l A.
- S2104S1983FirstMissing_of_stackWitness: same hypothesis -> S1983FirstMissing l A.

This removes the signature-label part of the honest target: no separate honest
signature witness is needed once an actual stack quotient witness is available.

## 4. Exact first missing

S2104HonestQuotientFirstMissing l A := Nonempty (S1971StackQuotientWitness l A).

S1971StackQuotientWitness contains:
- cF : HyperbolicOrbicurve (S1732A l).F;
- pointwise : for every test object U, an equivalence between cF.stack.fiber at U
  and the pointwise action-groupoid quotient S1971PointwiseQuotient U;
- quotient : OrbicurveSignInvariantMorphism A cF;
- witness : OrbicurveSignQuotientWitness A quotient.

The missing part is the actual quotient stack/fiber construction, not the
honest signature label.  S1971QuotientStack (functorial pointwise colimit plus
IsStack) is a related but not identical target; the witness includes the
quotient morphism and universal property.

## 5. S2103 prestack first missing

S2103D9PrestackActual already isolates:

  SlicePushNaturality M N
    := forall X1 X2 f,
         (sheafHom' M N).map f >> appFamily X2 =
           appFamily X1 >> (presheafHom M N).map f

and:

  S2103FirstMissing K
    := forall S M N, SlicePushNaturality M N.

Equivalently, there is a NatIso sheafHom' M N ~= presheafHom M N with the
canonical components.  S2103 proves:
- pointwise bijection sliceComparison_bijective;
- naturality_iff_exists_natIso;
- slicePushNaturality_iff_pullHom;
- SlicePushNaturality -> IsPrestack -> S2093SheafPrestack K.

The exact coherence missing is the compatibility of
GrothendieckTopology.overMapPullbackComp with
Over.iteratedSliceEquivOverMapIso (backward form), not a pointwise comparison.

## 6. No fake

- No IsStack instance is declared or claimed.
- No pointwise action groupoid is substituted for the quotient stack witness.
- No representable label-only orbicurve is used.
- The conditional theorems never assert their hypotheses.
- Axioms: propext, Classical.choice, Quot.sound.

## Verification

- EXIT=0
- SHA256: 387e7110552f5ffab46f7af6d6688ee3abb8127afac188bae0588a5ca532dfc3
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2104D9HonestQuotientActual.olean, size 51784
- axioms for all seven declarations: propext, Classical.choice, Quot.sound.
