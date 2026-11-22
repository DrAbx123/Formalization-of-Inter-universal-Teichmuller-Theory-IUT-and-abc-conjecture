# L1-F3 STAGE1: arbitrary l >= 5 elliptic torsion / full Tate declarations

## Scope and consumer
- Target fact: for an elliptic curve E over a field K and every prime label l with l >= 5, the l-torsion E[l] should have actual cardinality l^2 (equivalently, a rank-two ZMod l basis), and the full product over all l should exist as the arithmetic Tate module.
- Actual consumers:
  - `PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation` (Foundations/Geometry/EllipticTorsion.lean) consumes a supplied basis `(Fin 2 -> ZMod l) ~= X.LTorsion l`.
  - `TateModuleProfinite.tateLevelLGaloisMatrixRepresentation` specializes it to the concrete curve.
  - `SourceFullTateModuleData` (Example36EllipticCurveSourcePiCard.lean) is the frozen full-product structure; it has components `tateComponent l hl`, `proTwoTateModule`, `fullTateModule`, and factor maps, but no inhabitant and no consumer theorem.
  - `CurvePreGaloisCategoryRemainingFields` (Example36CurveGaloisCategory.lean) is unrelated to l-torsion; it is the G2 scheme-quotient card.

## Actual declarations found
- `PuncturedEllipticCurve.LTorsion l := AddSubgroup.torsionBy X.AlgebraicClosurePoint l.value` is actual; it has a constructed `Module (ZMod l.value)` instance.
- Actual absolute-Galois action:
  - `galoisActionOnPoint`
  - `galoisActionOnLTorsion`
  - `galoisActionOnLTorsionLinearEquiv`
  - `galoisActionOnLTorsionLinearEquivHom`
  - `galoisActionOnLTorsionGeneralLinearRepresentation`
- Conditional matrix representation:
  - `galoisLTorsionMatrixRepresentation (basis : (Fin 2 -> ZMod l.value) ~= X.LTorsion l)`
  - its continuity, open kernel, kernel subgroup/closed subgroup, kernel field, finite-Galois and number-field instances.
- Concrete level E[l]:
  - `TateModuleProfinite.tateLevelLTorsion l`
  - `tateLevelLGaloisLinearRepresentation l`
  - `tateLevelLGaloisGeneralLinearRepresentation l`
  - `tateLevelLGaloisMatrixRepresentation l basis`
- Frozen/pending cards:
  - `TateLevelLRankTwoBasisCard l` and `TateLevelLFiniteCard l` (Prop, no inhabitant).
  - Audit obligation `ellipticLTorsionRankTwoBasis` status pending.
  - `ProLTateModuleProjSystemData` (general l >= 5, no inhabitant; l = 2 is actual).
  - `SourceFullTateModuleData` (no inhabitant).

## Exact gaps
1. No theorem gives `Finite (X.LTorsion l)` or `Nat.card (X.LTorsion l) = l.value ^ 2` for l >= 5.
2. No theorem gives `Nonempty ((Fin 2 -> ZMod l.value) ~= X.LTorsion l)`; this is the pending audit obligation.
3. No general pro-l inverse system `E[l^(n+1)] -> E[l^n]`, no limit `T_l(E)`, and no full product `prod_l T_l(E)`; only l = 2 pro-2 data is actual.
4. No identification of a Tate module with the geometric fundamental group of the once-punctured curve (correctly absent).

## Minimal next declaration
Recommended next statement (stage 2, actual objects, no new assumptions beyond Mathlib's elliptic-curve/algebraic-closure setting):

```lean
theorem ellipticLTorsion_card_eq (X : PuncturedEllipticCurve K)
    (l : PrimeGeFive) :
    Nat.card (X.LTorsion l) = l.value ^ 2
```

An equivalent and more directly consumable form is the rank-two basis:

```lean
theorem ellipticLTorsion_rankTwoBasis (X : PuncturedEllipticCurve K)
    (l : PrimeGeFive) :
    Nonempty ((Fin 2 -> ZMod l.value) ~= X.LTorsion l)
```

The basis form feeds `galoisLTorsionMatrixRepresentation` immediately. The cardinality form plus `Module.finrank` reasoning should feed the basis form; both are absent from Mathlib 4.32.2. Only `propext`, `Classical.choice`, `Quot.sound` are expected in any eventual proof.

## Consumer ranking
- Primary: matrix representation / kernel field for arbitrary l >= 5.
- Secondary: `SourceFullTateModuleData` full product (requires pro-l systems for all l, a much larger gap).
- Not a consumer: scheme-level G2 `CurvePreGaloisCategoryRemainingFields`; that is a different quotient/colimit statement and must not be conflated with the source orbicurve G2.

## Status
- statement_compiles: no new Lean declarations added (documentation only).
- proof_body_checked: not applicable.
- kernel_closed: no.
- target_accepted: no.
