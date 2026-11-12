# S1193: audit of S1184 single-factor non-refl Kummer iso

Date: 2026-10-30.  Scope: `S1184NonReflKummerActual.lean`, its use for a
single-factor `upperEnv`, and the failed common-group extension
`S1187NonReflKummerCommonGroupActual.lean`.  No weak wrapper written.

## 1. S1184 status: actual, but non-refl is not proved

`S1184NonReflKummerActual.lean` compiles: `lake env lean` EXIT=0.

For `φ : FPrimeStripEquiv upper lower` and a place `v`, it constructs:

```text
stripEquivKummerIso φ v :
  TimesMuKummer.Isomorphism
    (upper.unitsAction v)
    ((lower.unitsAction v).comp (φ.isoPi v))
```

with

```text
equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
equivariant := φ.compatAction ...
invariantImage := fixedSubgroup mapping ...
```

This is a genuine construction, not `TimesMuKummer.Isomorphism.refl` and not
a conjugation of `refl`.  It is actual **as data for any supplied φ**.

However S1184 does **not** prove that this isomorphism is non-refl.  Its only
theorem is `stripEquivKummerIso_equiv` (the `equiv` field formula).  If
`φ.isoMon v` is the identity (e.g. `φ` reflexive), the construction is
refl-shaped.  There is no theorem that the actual source link
`I.fLinkAt 1 0 1 1` has nontrivial `isoMon` at the relevant place.  So
"actual non-refl" is not established; only "actual constructed iso from φ".

## 2. Direct use for a single-factor upperEnv

`upperEnv` (`S1180ActualUpperEnv.lean:42-47`) is:

```text
sourceEvaluationArrowOfUnitPortion
  (I.fLinkAt 1 0 1 1)
  (unitPortion from a SourceTimesMuKummerLayer)
```

and `upperEnv.unitPortion` requires a `SourceTimesMuKummerLayer` over all
`v : V` with one common group `G` and actions

```text
sourceAction : ∀ v, G →* MulAut ((upper.Mon v)ˣ)
targetAction : ∀ v, G →* MulAut ((lower.Mon v)ˣ)
```

With S1184 alone, the natural single-factor layer is only:

```text
G := upper.Pi v                         -- depends on v
sourceAction := upper.unitsAction v
targetAction := (lower.unitsAction v).comp (φ.isoPi v)
kummer := stripEquivKummerIso φ v
```

This works only for a **single fixed factor** (one-place V, or restricting
the whole construction to one `v`).  Then `ofKummerLayer` +
`sourceEvaluationArrowOfUnitPortion φ` give a one-factor evaluation arrow, and
`upperEnv` can use it at that factor.

It cannot be plugged directly into S1180's `upperEnv` over general `V`:
`G = upper.Pi v` changes with `v`, and S1180's group is
`ActualKummerGroup = (v : V) → upper.Pi v`.  S1184 supplies no common-group
action family and no `SourceTimesMuKummerLayer` over all `v`.

## 3. Product extension not needed; common-group layer is the gap

S1185's `LowerKappaDonor`/product pair group is not the right extension here;
the single-factor data is per place, and no product over upper/lower factors
is needed for the local statement.

`S1187NonReflKummerCommonGroupActual.lean` does attempt the non-product common
group

```text
GraphGroup := (v : V) → upper.Pi v
factorUpper v := eval at v
factorLower φ v := (φ.isoPi v).comp (eval at v)
```

and constructs a candidate `kummerIsoAt φ v`.  But it does **not compile**:
EXIT=1 at `S1187NonReflKummerCommonGroupActual.lean:102`, where the reverse
inclusion of `invariantImage` needs
`eU.symm u ∈ fixedSubgroup ((upper.unitsAction v).comp (factorUpper v)) H`;
the current data only gives a quotient-level `invariantImage`, not the
unit-level fixed-subgroup preimage law.  So the graph common-group layer is
not actual either.

## 4. First type/theorem gap

The first missing object for a global single-factor upperEnv is:

```text
SourceTimesMuKummerLayer G upper lower
```

for a common group `G` over all places, with actual fields:

```text
sourceAction : ∀ v, G →* MulAut ((upper.Mon v)ˣ)
targetAction : ∀ v, G →* MulAut ((lower.Mon v)ˣ)
kummer : ∀ v, TimesMuKummer.Isomorphism (sourceAction v) (targetAction v)
```

and the `kummer v` must be the actual source Kummer isomorphism, not
`refl`/conjugated-refl.  For the graph candidate, the first missing theorem
is the unit-level fixed-subgroup reverse inclusion used in S1187's
`invariantImage` (there is no `fixedSubgroup` preimage theorem in the tree).

For a strictly single-factor (one-place) upperEnv, S1184 already suffices
after narrowing the place type to that factor; no product construction is
needed.  What remains there is only the nontriviality/non-refl witness for
the chosen actual `φ`.

## Verdict

```text
S1184 single-factor iso        actual (EXIT=0)
S1184 non-refl claim           NOT proved
single-factor upperEnv         usable after restricting to one place
global upperEnv over V         NOT direct; common-group layer missing
S1185 product pair extension   not needed for this single-factor question
S1187 graph common-group       not actual (EXIT=1, invariantImage
                               fixed-subgroup reverse inclusion)
first gap                      common-group SourceTimesMuKummerLayer with
                               actual kummer, and nontriviality of φ
wrapper written                none
```
