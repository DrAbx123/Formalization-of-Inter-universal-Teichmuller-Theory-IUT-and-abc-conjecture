# Single-sorry line: no-sorry inventory (A974/A977)

## 1. Status: single-sorry line STOPPED

Per user instruction (A977), the sorry-based chain was stopped and its files moved out of
the formal directory:
- `tmp/sheaf/xif/paper/Mzk1IUTModuloInequalityActual.lean` ->
  `tmp/sheaf/xif/paper/_DRAFT-Mzk1IUTModuloInequalityActual.lean` (underscore, unregistered)
- `tmp/sheaf/xif/paper/Mzk1IUTModuloSSIneq.lean` ->
  `tmp/sheaf/xif/paper/_DRAFT-Mzk1IUTModuloSSIneq.lean` (underscore, unregistered)
No sorry file remains registered; no further sorry chain is being built.

## 2. Existing no-sorry consumers of SSIneq/variant (repo-wide)

| file:line | declaration | signature | olean |
|---|---|---|---|
| `tmp/sheaf/xif/paper/Mzk1SSIneqConsumerChainActual.lean:27` | `abcConjecture_of_forall_ssIneq` | `(forall D, SSIneq D) -> ABCConjecture` (via Iut consumers) | **False** (needs lana `Iut.WallEquiv.Basic`) |
| same:33 | `cor312VariantHolds_of_forall_ssIneq` | `(forall D, SSIneq D) -> Iut.Cor312VariantHolds` | **False** |
| `tmp/sheaf/xif/paper/Mzk1FinalABCBridgeActual.lean:26` | `classicalABC_implies_ABCConjecture` | `Iut.ClassicalABC -> ABCConjecture` | **False** (imports `Iut.MainTheorem`) |
| same:36 | `abc_of_cor312VariantHolds` | `Iut.Cor312VariantHolds -> ABCConjecture` | **False** |
| `tmp/sheaf/xif/paper/Mzk1ClassicalABCToOurABCActual.lean` | `abcConjecture_of_classicalABCShape` | `ClassicalABCShape -> ABCConjecture` | **TRUE (green)** |
| `tmp/sheaf/xif/paper/Mzk1PaperToClassicalABCActual.lean:89` | `paperGap_to_cor312Conclusion` | `paperGap D -> Cor312Conclusion ...` | **TRUE (green)** |
| same:101 | `classicalABCShape_to_ABCConjecture` | `ClassicalABCShape -> ABCConjecture` | **TRUE (green)** |

lana source side (root `Iut/`, reference only; oleans of `Iut/WallEquiv/*` not built):
- `Iut/MainTheorem.lean:13` `classicalABC_of_variant : Cor312VariantHolds -> ClassicalABC`;
- `Iut/Cor312/Concrete/ThetaRegion.lean:375` `def Cor312VariantHolds`;
- `Iut/WallEquiv/Gap.lean:543` `variant_of_ss_gap (h : SSIneq D) : Corollary312Variant (concreteVariantData D)`;
- `Iut/WallEquiv/Gap.lean:26` `variant_iff_le_rhs`.

## 3. ABC target type

`ABCConjecture` is defined at `LeanFormal/IUT/ABCBridge/Bridge/Statement.lean:32-35`
(with `ABCInequality` :28-29, `radical := natRadical` :24, `IsABCTriple := PrimitiveAdditiveTriple` :26).
Existing consumers: `Mzk1ClassicalABCToOurABCActual.abcConjecture_of_classicalABCShape`,
`Mzk1FinalABCBridgeActual.classicalABC_implies_ABCConjecture`/`abc_of_cor312VariantHolds`,
`Mzk1PaperToClassicalABCActual.classicalABCShape_to_ABCConjecture`.

## 4. Judgment: shortest no-sorry chain

Two candidate assemblies, both needing NO sorry and NO class-B hypothesis:

(A) lana-style: `forall D, SSIneq D` -> (pointwise `Iut.WallEquiv.variant_of_ss_gap`)
    `Iut.Cor312VariantHolds` -> (`Mzk1FinalABCBridgeActual.abc_of_cor312VariantHolds`, or
    `Iut.classicalABC_of_variant` + `classicalABC_implies_ABCConjecture`) -> `ABCConjecture`.
    BLOCKER: requires lana oleans `Iut/MainTheorem.lean` and `Iut/WallEquiv/*`;
    `Mzk1FinalABCBridgeActual` and `Mzk1SSIneqConsumerChainActual` currently have olean=False.

(B) local paper-side: `Paper312Statement`/`paperGap` -> (`paperGap_to_cor312Conclusion`)
    `Cor312Conclusion` -> ??? -> `ClassicalABCShape` -> `ABCConjecture`.
    BLOCKER: the edge `Cor312Conclusion -> ClassicalABCShape` is missing
    (`Mzk1PaperToClassicalABCActual.edgeRows`, MissingEdge_cor312Conclusion_to_classicalABCShape);
    this is exactly the class-B edge used previously, but no green theorem fills it.

Conclusion: an existing green theorem set cannot yet replace the missing edge; the shortest
no-sorry path is (A) once the lana `Iut/MainTheorem`/`Iut/WallEquiv` oleans exist.  Until then
a class-B hypothesis (not an axiom) is required for any local assembly.
