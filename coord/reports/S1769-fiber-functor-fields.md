# S1769 -- fiber functor fields for `CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)`

Date: 2026-11-01. Worker: S1769.

## Deliverable

- Lean file: `tmp/sheaf/xif/paper/S1769FiberFunctorFieldsActual.lean`
- Source SHA256: `B8F04BFA86CFB068F6CDBB097ADEEB4287B7114F4A92A5B461291B2C2535C732`
- `lake env lean` EXIT=0.
- Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1769FiberFunctorFieldsActual.olean`
  - 260392 bytes
  - SHA256 `73EFB63AA1A7284BDE261FF9B2F5586845B8BC097BFDECFFBB917F032D228C8C`
- Axioms of every audited declaration: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, new `axiom`, or weakened statement in the source.

## Six-field status

| field | status in this file |
|---|---|
| `preservesTerminalObjects` | **proved** (unconditional modulo `[PreGaloisCategory C]`) |
| `preservesPullbacks` | reduced to `BCPreservesPullbacks K` |
| `preservesFiniteCoproducts` | reduced to `BCPreservesFiniteProducts K` |
| `preservesEpis` | reduced to `BCPreservesEpis K` |
| `preservesQuotientsByFiniteGroups` | reduced to `BCPreservesQuotients K` |
| `reflectsIsos` | **proved** (unconditional modulo `[PreGaloisCategory C]`) |

All four reductions are theorems (`preservesPullbacks_of`, `preservesFiniteCoproducts_of`,
`preservesEpis_of`, `preservesQuotients_of`), and the conditional assembly is
`S1769.fiberFunctorOf`.

## Exact first missing

In the order of the task the first missing field is `preservesPullbacks`.  Its exact
remaining input is

```lean
def BCPreservesPullbacks (K : Type) [Field K] : Prop :=
  PreservesLimitsOfShape WalkingCospan (CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)).op
```

i.e. base change along `K -> Kbar` preserves pushouts (equivalently, its opposite preserves
pullbacks).  The other three missing conditions are listed in the file (`BCPreservesFiniteProducts`,
`BCPreservesEpis`, `BCPreservesQuotients`).

## Mathematical route for the four conditions

The reductions use Mathlib's
`CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber`

  `fiber K Kbar ~= (baseChange K Kbar).op >>> fiber Kbar Kbar`,

and the fact that `fiber Kbar Kbar` is an equivalence (`equivOfIsSepClosed`, since `Kbar` is
separably closed).  Hence the six fields of `fiber K Kbar` follow from the corresponding
properties of `baseChange K Kbar`.

For the four base-change conditions, Mathlib already contains the ambient statements in
`Mathlib/Algebra/Category/Ring/Under/Limits.lean`:

* `CommRingCat.Under.tensorProd` is `Kbar (x)_K -` up to natural isomorphism;
* it preserves finite limits when `K -> Kbar` is flat (`tensorProdMapEqualizerForkIsLimit`, and
  the finite-products instance);
* `Under.pushout` is left adjoint to `Under.map`, hence preserves colimits.

The remaining work is therefore purely the transfer through the full subcategory
`CommAlgCat.FiniteEtale K` (finite etale algebras are closed under the relevant finite limits and
finite colimits), not new algebra.  For `preservesQuotientsByFiniteGroups` the recently
available S1770 (`S1770FiniteEtaleFixedPointsActual.lean`) supplies the fixed-point algebra and
its limit cone, which is the natural input for the quotient case.

## Caveats

* The ambient `PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op)` instance is not constructed
  in this file; it enters as the typeclass variable `[PreGaloisCategory (C K)]`, exactly as in
  S1749/S1767.  The fiber-functor fields are stated at that instance.
* An import check of the generated olean was attempted; the primary source compiles EXIT=0,
  but the import-check file hit transient missing `.olean.private` files under
  `lake/packages/mathlib/.lake/build` while another process was touching the Mathlib build tree.
  This is an environment artifact, not a failure of the S1769 source (which recompiled EXIT=0
  after the check).
