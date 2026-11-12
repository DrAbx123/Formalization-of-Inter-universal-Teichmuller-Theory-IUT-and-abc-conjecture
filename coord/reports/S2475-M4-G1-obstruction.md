# S2475: M4/G1 actual construction obstruction

Date: 2026-11-03. Layer O (S2046 M4/G1). No new interface file and no new
compile. This report records the concrete obstruction after the S2442 action
became available.

## G1: why S2473G1EquivariantComparisonRequired cannot be constructed from
## the current API

Actual data:

```text
S2442MuHatAction  : Gv p →* MulAut (muHatZ p)         (S2442/S2471)
S2046G1PsiCnsAction : Gv p →* MulAut (PsiCnsCyclotome p) (S2046)
S2442MuQZAction_compat : action on muQZ is compatible with stage conjugation
```

The needed object is:

```text
comparison : muHatComparison p
equivariance :
  ∀ g x, comparison (S2442MuHatAction p g x) =
    S2046G1PsiCnsAction p g (comparison x)
```

Current `muHatComparison p` is only:

```text
Nonempty (muHatZ p ≃* PsiCnsTorsionCyclotome p)
```

Concrete obstruction:

1. There is no actual comparison map in the tree; only a `Nonempty` proposition.
2. `S2046G1ModuleEquivOfComparison` obtains its equivalence by
   `Classical.choice` from that proposition. The chosen equivalence has no
   relation to `S2442MuHatAction` or `S2046G1PsiCnsAction`.
3. The two actions live on different actual carriers:
   - `S2442MuHatAction` acts on
     `muHatZ = KummerCyclotome (Multiplicative (muQZ p))`;
   - `S2046G1PsiCnsAction` acts on `PsiCnsCyclotome p`.
   The only bridge in the tree is the missing local-reciprocity comparison
   `muQZComparison p` / `muHatComparison p`, and it carries no naturality.
4. `S2442MuQZAction_compat` only relates the muQZ action to stage
   conjugation; it does not produce a map from `muQZ` to the torsion units of
   the local integral monoid, hence cannot define the comparison.
5. An arbitrary group isomorphism between two `Hom(Q/Z,-)`-type cyclotomes
   need not intertwine the two `G_v`-actions. Thus equivariance is not a
   consequence of `Nonempty` and cannot be proved for the
   `Classical.choice` equivalence without additional naturality.

**Exact first missing / obstruction:**

```text
a natural comparison muQZ ≅ torsion units,
or equivalently a natural muHatComparison with action compatibility
```

This is exactly the `S2473G1EquivariantComparisonRequired` content; it is
not derivable from the current Nonempty comparison.

Topology/continuity remains additionally missing:

```text
TopologicalSpace (muHatZ p)
Continuous action of Gv on muHatZ p
Continuous comparison
```

No topology is declared on muHatZ in the tree.

## M4: why S2136M4NormalizationData cannot be constructed

Actual data:

```text
S2136H2ZHatEquiv : H^2(Qp, Ẑ(1)) ≃* Ẑ
S2136BrEquivQZ   : Br(Qp) ≃* Q/Z
PsiCnsKummer p   : actual Kummer map
Kummer image / nonnegative cone : actual
```

Needed:

```text
norm : PsiCnsCohomology p →* Multiplicative Zhat
surjective
mrange (PsiCnsKummer p) = comap norm zhatNatMonoid
kernel_units
```

Concrete obstruction:

1. The H2/Br equivalences are degree-two module comparisons. They do not give
   a map from the degree-one limit `PsiCnsCohomology p` to `Zhat`.
2. There is no cup-product pairing or H2 class API in the tree that could
   define `norm`.
3. The Kummer image describes a submonoid of the degree-one limit but does not
   define a map on all of `PsiCnsCohomology p`; no extension/normalization
   theorem is available.
4. Therefore neither `surjective` nor `kummer_image` nor `kernel_units` is
   provable from existing data.

**Exact first missing:**

```text
S2136M4NormalizationData p
  norm, surjective, kummer_image, kernel_units
```

No fake trivial norm or arbitrary map is used.

## Status

- G1 algebraic action: actual.
- G1 natural equivariant comparison: blocked by missing natural
  `muQZComparison`; exact content is `S2473G1EquivariantComparisonRequired`.
- G1 topology/continuity: missing topology on `muHatZ`.
- M4 normalization: blocked by missing cup-product/H2-class map; exact content
  is `S2136M4NormalizationData`.
- No new interface file was produced in this turn; no fake/conditional target.

## Next executable step

The only genuine next step is to construct the natural local-reciprocity
comparison itself (M4/G1 shared input), or to add the cup-product normalization
API. Without one of these, M4/G1 remain exact missing.
