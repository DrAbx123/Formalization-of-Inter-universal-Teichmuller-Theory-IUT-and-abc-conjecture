# S2758 — clauseA–F actual-supplier audit for canonical Gaussian T

Date: 2026-11-07. Audit only; no T shell construction.

## 0. T field list

`SourceNativeInitialThetaData` needs 11 fields:

```lean
arithmetic, tuple, clauseA, clauseB, clauseC, clauseD, clauseE, clauseF
-- (tuple itself bundles fbar + source/sign quotient + xF/cK/V/epsilon)
```

The only constructor chain found is
`SourceCompletion.toSourceNativeInitialThetaData`, itself requiring a full
`SourceCompletion` (arithmetic, fbar, signQuotient, arithmeticPrelude,
clauseA–F).  There is no partial constructor.

## 1. Actual suppliers available

| field/data | actual? | supplier |
|---|---|---|
| `arithmetic := gaussianInitialThetaArithmeticData` | YES | ConcreteArithmeticExample |
| Gaussian curve `gaussianPuncturedCurve` | YES | ConcreteArithmeticExample |
| `SourceFbarExtension` (canonical) | YES | `SourceFbarExtension.canonical` |
| `SourceSignQuotientData` / `SignQuotientGeometricCore` G | NO | no constructor from arithmetic; requires actual orbicurves, sign action, quotient, groups, extensions, cusp |

## 2. Clause-by-clause suppliers

| clause | constructor | required supplier fields | actual supplier? |
|---|---|---|---|
| A | `SourceClauseA.ofGoodOrMultiplicativeReduction` | reductionCases (∀ finite p, good or multiplicative), fieldOfModuli, maximalSolvableExtension + property + contains | NO |
| B | `SourceClauseB.ofTateComparisonWitnesses` | multiplicative over bad, Tate comparison witness for each bad p, residue char coprime to l | NO |
| C | `SourceClauseC.ofCanonicalRepresentation` | torsion23 rational, rank-two torsion basis, SL2 image containment, kernel-field identification `A.K ≃ₐ[A.F] galoisLTorsionKernelField`, range equality | PARTIAL actual objects exist only from an existing clauseC (circular); no standalone Gaussian supplier |
| D | `SourceClauseD.ofKFields` (K-side) | K sign action/quotient/extensions, torsion cover, K groups, group inclusion, x/c-to-F embeddings | NO |
| E | `SourceClauseE.ofLocalFamilies` | finiteLocal and infiniteLocal source families for every selected place | NO |
| F | `SourceClauseF.ofCanonicalBoundaryData` | origin map, epsilon equality, cuspidal decomposition, origin equality | NO |

## 3. Gaussian obstruction for Clause C

For `gaussianInitialThetaArithmeticData`, `Fmod = F = K = GaussianField`
(QQ(i)).  Clause C demands

```lean
kernelFieldIdentification : A.K ≃ₐ[A.F]
  A.curve.galoisLTorsionKernelField l torsionBasis
```

with `A.K = A.F`, hence it forces the l-torsion kernel field to be `F` itself.
For `l >= 5` the mod-l Galois representation has nontrivial kernel field, so
this identification is not available for the Gaussian K=F arithmetic.  This
matches S1539-promachina-gaussian-audit: local Gaussian data K=F is
incompatible with Clause C + SL2 large image.

Thus clause C is not merely missing an actual supplier: the Gaussian K=F
arithmetic is the wrong arithmetic input for the paper Clause C.

## 4. Minimal constructible field list

Constructible now (actual):

1. `arithmetic := gaussianInitialThetaArithmeticData fiveLabel`;
2. `fbar := SourceFbarExtension.canonical`;
3. Gaussian curve (`gaussianPuncturedCurve`).

Remaining fields (all needed before a T exists):

1. `signQuotient` / G: actual xF, geometry, sign action, quotient, groups,
   scalar extensions, cusp; no actual supplier.
2. clauseA: reduction cases + fieldOfModuli + maximal solvable extension.
3. clauseB: multiplicative bad reduction + Tate witnesses + residue coprimality.
4. clauseC: torsion basis + SL2 image + kernel field identification;
   IMPOSSIBLE for Gaussian K=F (see section 3), needs a different arithmetic A.
5. clauseD: K-side groups/sign action/torsion cover/embeddings.
6. clauseE: finite/infinite local source families.
7. clauseF: boundary origin map + cusp decomposition.
8. `arithmeticPrelude` for SourceCompletion;
9. `SourceCompletion` itself, then T.

## 5. S2757 conditional result (not an actual T)

`S2757CanonicalGaussianTActual` proves only the conditional constructor

```lean
SourceCompletion.{0} fiveLabel ->
C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel ->
SourceNativeInitialThetaData.{0} fiveLabel
```

with `T.arithmetic = gaussian...` and `T.arithmetic.K = GaussianField`.
It is NOT an actual T: no `SourceCompletion` with Gaussian arithmetic exists.

## 6. Verdict

- Minimal actual pieces: arithmetic, canonical fbar, Gaussian curve.
- signQuotient and clauseA–F have NO actual suppliers for the Gaussian input.
- Clause C has a structural obstruction (K=F), so the canonical Gaussian T is
  not the right object for the full source contract.
- Do not construct a T shell or claim canonical T actual.
