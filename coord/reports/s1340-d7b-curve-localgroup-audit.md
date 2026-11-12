# S1340: D7b curve-side localGroupCarrier audit

Date: 2026-10-30.  Read: S1331OrbicurveClauseAudit, S1331 residual fields,
S1331/S1319 probes, `SourceDefinition31LocalValuationSections`,
`SourceDefinition31Boundary` D7 fields, `SourceDefinition31D4D9Supply` D7b,
`CurveEtaleFundamentalGroup`.

## Verdict

The D7b curve-side local-group carriers

```text
localGroupCarrier : valuationCarrier → Type
modifiedLocalGroupCarrier : modifiedValuationCarrier → Type
localGroupSection : pointwise bijection Pi_Xv inside Pi_Cv
```

cannot be constructed from the actual D6 data in the tree, because **no actual
D6 orbicurve clause exists**.  S1319/S1331 audit does not construct D6.

## 1. What S1331 actually has

`S1331OrbicurveClauseAudit` constructs only:

* `S1331ClauseCurve l = (S1280Arithmetic l).curve.curve.toProjective.Point`
  (actual curve point carrier);
* the actual punctured-curve inclusion;
* the exact-sequence base group `Iut.AbsoluteGaloisProfinite A.K` (an
  arithmetic Galois group, not a curve/orbicurve Pi).

Everything else of D6 is the exact residual structure:

```text
S1331ResidualFields l where
  cover : Type
  structureGroup : Type
  coverToPunctured : cover → puncturedCurve
  cover_surjective : Surjective coverToPunctured
  exactSequence : S1331ExactSequenceResidual l
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  curveCompatibility : Prop
  curveCompatibility_proved : curveCompatibility
```

None of these has an inhabitant.  There is no actual orbicurve stack, no
actual finite etale cover with structure group, no orbifold cusp data, and no
actual `Pi_Xv`/`Pi_Cv`.

## 2. Why the available curve Pi is not enough

`CurveEtaleFundamentalGroup.curveEtaleFundamentalGroup` is an actual group: the
automorphism group of the geometric fiber functor of the once-punctured
curve `y^2 = x^3 - x`.  It is:

* for a different curve than the S1280 D6 curve `y^2 + xy = x^3 + 5`;
* the fiber-functor automorphism group, not a profinite/orbicurve Pi;
* a single geometric object, not the D6 orbicurve `G2`/`Pi_Xv` family.

Using it as `localGroupCarrier` would substitute a different curve's topological
fundamental group, contrary to the original D7b object.

## 3. Arithmetic G_v is not Pi_Xv

The S1331 exact-sequence base group is:

```text
Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).K
```

This is the arithmetic local Galois group `G_v` (or its global analogue), not
the curve-side etale fundamental group `Pi_Xv` of the D6 orbicurve, and not the
`Pi_Xv` inside `Pi_Cv` of D7b.  It must not be used for
`localGroupCarrier`.

## 4. First exact field

The first missing object is the actual D6 orbicurve clause (or an equivalent
actual D6 geometric realization), specifically:

```text
cover : Type
structureGroup : Type + Group structureGroup
coverToPunctured : cover → puncturedCurve
cover_surjective : Surjective coverToPunctured
exactSequence : S1331ExactSequenceResidual l
cuspCount + positivity
```

Only after this can one define:

```text
localGroupCarrier x := Pi_1^et(orbifold X_x)
modifiedLocalGroupCarrier w := Pi_1^et(orbifold C_w)
localGroupSection : Pi_Xv ↪ Pi_Cv
```

None of these carriers is determined by the S1280 arithmetic data alone.

## 5. Status

```text
actual D6 curve point carrier        yes (S1331)
actual D6 orbicurve clause           absent
actual D6 etale/Pi_Xv carrier        absent
D7b localGroupCarrier                not constructible
arithmetic G_v as Pi_Xv              forbidden
CurveEtaleFundamentalGroup           different curve, not D6 Pi
first exact field                    S1331ResidualFields (D6 cover/group/
                                     exactSequence/cusp)
new Lean                             none
```

## 6. Recommendation

Stop at the actual D6 orbicurve construction.  Do not fill D7b with:

* `AbsoluteGaloisProfinite` (arithmetic G_v);
* the `y^2 = x^3 - x` curve fiber-functor group;
* an arbitrary Type/PUnit for the local-group carriers.

Once D6 has actual orbicurves and finite etale covers, D7b should be built from
their actual etale fundamental groups; until then `localGroupCarrier` remains an
exact source field.
