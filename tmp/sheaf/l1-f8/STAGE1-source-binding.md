# STAGE 1 — L1-F8 source binding: ThetaLinkSourceCoverConsumer fields vs actual source

Status: phase-1 scope record only. No production edit, no Lean file created, no `SliceFactorization` assumed. This is a child node of L1-F8; the parent consumer remains unclosed until its dependency and this binding exist.

Sources read:
- coord/LAYER1-PLAN.md (L0.5, L1-F8)
- LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean (donor categorical model)
- LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean (`SourceCompletionSignQuotient`)
- tmp/n8-20261018/general/ActualSourceThetaLink.lean (actual local field/curve q-data and explicit ATheta residual)
- Iut/Foundations/SourceSemiGraphOfAnabelioids.lean (structure `SourceSemiGraphOfAnabelioids`)

## 1. Consumer fields — exact Lean types

From `tmp/sheaf/l1-f8/ThetaLinkSourceCoverConsumer.lean`:

| field | exact type |
|---|---|
| `diagram` | `Iut.SourceSemiGraphOfAnabelioids.{u}` |
| `root` | `diagram.base.Vertex` |
| `Yddot` | `ConnectedTemperedCover diagram root` (full subcategory of `TemperedCover diagram root` under `ConnectedTemperedCover`; underlying `diagram.CovObject`) |
| `model` | `BaseFieldCoverModel diagram root` |
| `data` | `ThetaProductData diagram root Yddot model` |
| `factorization` | `SliceFactorization data` |
| conclusion | `BaseCover model ≌ ThetaCoverSubcategory data` (`thetaEquivalence data factorization`) |

`SourceSemiGraphOfAnabelioids` is the literal semi-graph of connected anabelioids: `base : SourceSemiGraph`, vertex/edge anabelioids, branch morphisms, and branch π₁-monomorphisms.

## 2. Actual source objects available

### 2.1 Sign-quotient/curve side

`SourceCompletionSignQuotient (A : InitialThetaArithmeticData l)` stores:
- `xF : Iut.HyperbolicOrbicurve A.F`;
- `xF_geometry : SourceOncePuncturedGeometry A.curve xF`;
- `xFGroups : SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite A.F)`;
- sign quotient `cF`, `signAction`, `quotient`, `quotientWitness`;
- `xK/cK` over `A.K` and the boundary cusp `epsilon : Iut.OrbicurveBoundaryCusp cK`.

### 2.2 Local actual theta side

`ActualSourceThetaLink.lean` provides:
- `K : Type u`, `[Field K] [NumberField K]`, `v : NumberField.FinitePlace K`;
- `X : PuncturedEllipticCurve K`, `hsplit : X.HasSplitMultiplicativeReductionAt v`;
- `SourceLocalField v := NormalizedCompletion v`;
- `sourceQv : SourceQv ...` and `sourceQ : SourceLocalField v`;
- `SourceThetaRootData` and `sourceOddTheta_normalized` (actual local normalized odd theta).

### 2.3 Actual ATheta

There is **no Lean type for ATheta** in production. `ActualSourceThetaLink.lean` explicitly records the residual: an actual source cover object ATheta (product `Yddot_v × A` over the actual tempered source graph) and its structure morphisms, integral units, theta divisor, and finite-layer Kummer square are not constructed.

## 3. Exact binding gaps

| consumer field | needed actual object/statement | current Lean situation | exact gap |
|---|---|---|---|
| `diagram` | construction `sourceDiagram (xF : HyperbolicOrbicurve A.F) : SourceSemiGraphOfAnabelioids` | `SourceSemiGraphOfAnabelioids` exists; no production construction from `xF` or from a curve | no map from the source orbicurve/curve to the semi-graph of anabelioids |
| `root` | a vertex of `sourceDiagram.base` (marked cusp/point) | `SourceSemiGraph.base.Vertex` exists inside the unknown diagram | no construction of the marked vertex |
| `Yddot` | connected tempered cover over `sourceDiagram`/`root`; intended universal/root cover of `X_v` | `ConnectedTemperedCover` and `temperedCovInclusion` exist; no construction from `xF` | no actual `TemperedCover`/`CovObject` object for the curve, no connectedness proof |
| `model` | `BaseFieldCoverModel diagram root`, i.e. predicate `IsBaseFieldCover`, base object, and proof it satisfies the predicate, tied to `K_v`/`A.F` | structure exists only as explicit donor input | no predicate from the actual base field, no base object |
| `data` | `ThetaProductData diagram root Yddot model`: product objects `Yddot × A`, projections, lift, universal property, `snd_epi` | structure exists only as donor input | no actual products of connected tempered covers; connected covers do not have global binary products |
| `factorization` | proof of `SliceFactorization data` from the base-field condition | only `productFunctor_full` consumes it; no proof in production | must be proved, not assumed |
| ATheta | actual source cover object/product `Yddot_v × A` and its structure morphisms | no Lean type; residual recorded in `ActualSourceThetaLink.lean` | full construction missing |

The binding cannot be identified by `rfl` or a type cast: `xF` is a `HyperbolicOrbicurve`, while `diagram` is a semi-graph of anabelioids; `SourceCompletionSignQuotient` does not contain a `SourceSemiGraphOfAnabelioids`.

## 4. Minimal writable statements (stage 2 candidates, not created)

Each declaration is a separate child node. They must remain statements with explicit named `sorry` until their source constructions exist.

```lean
-- F8a
def sourceDiagram {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) : Iut.SourceSemiGraphOfAnabelioids.{u}

-- F8b
def sourceRoot {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) (d : Iut.SourceSemiGraphOfAnabelioids.{u})
    (h : d = sourceDiagram xF) : d.base.Vertex

-- F8c
def sourceYddot {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) :
    ThetaLinkSourceCover.ConnectedTemperedCover (sourceDiagram xF) (sourceRoot xF)

-- F8d
def sourceBaseFieldModel {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) :
    ThetaLinkSourceCover.BaseFieldCoverModel (sourceDiagram xF) (sourceRoot xF)

-- F8e
def sourceProductData {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) :
    ThetaLinkSourceCover.ThetaProductData (sourceDiagram xF) (sourceRoot xF)
      (sourceYddot xF) (sourceBaseFieldModel xF)

-- F8f
theorem sourceSliceFactorization {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (xF : Iut.HyperbolicOrbicurve A.F) :
    ThetaLinkSourceCover.SliceFactorization (sourceProductData xF)
```

ATheta itself must be a separate definition of a `BaseCover model`/`ThetaCoverSubcategory data` object, not a field of the donor consumer.

## 5. Real consumer chain

`SourceCompletionSignQuotient.xF`/`xFGroups` -> source G2 / `OrbicurveEtaleFundamentalGroup` (L0.3) -> actual ATheta/Theta-link source (L0.5) -> `ThetaLinkSourceCoverConsumer` equivalence -> `ThetaLinkAssembly` abstract monoid link.

Current break points:
1. no `sourceDiagram` from `xF`;
2. no `Yddot`/base-field model/product data/SliceFactorization;
3. no ATheta object;
4. no bridge from the donor categorical equivalence to `ThetaLinkAssembly.thetaLink`;
5. L1-F8 consumer itself is blocked on the red production `ThetaLinkSourceCover` olean (see `CHILD-theta-source-cover-dependency.md`).

## 6. Node-local status and next child

Parent L1-F8: stage2 statement written, not compiled; remains unclosed.

Child nodes to register:
- `L1-F8a-source-diagram`: stage1/2, required construction `sourceDiagram` from `xF`;
- `L1-F8b-source-yddot`: stage1/2, actual connected tempered cover;
- `L1-F8c-base-field-model`: stage1/2, actual `K_v` predicate/base object;
- `L1-F8d-theta-product-data`: stage1/2, actual products `Yddot × A`;
- `L1-F8e-slice-factorization`: stage2, prove `SliceFactorization` (do not assume);
- `L1-F8f-ATheta`: stage1/2, actual ATheta cover object/residual;
- existing `CHILD-theta-source-cover-dependency`: production donor repair.

Recommended next executable child: `L1-F8a-source-diagram`, because every other field depends on the actual `SourceSemiGraphOfAnabelioids` construction.
