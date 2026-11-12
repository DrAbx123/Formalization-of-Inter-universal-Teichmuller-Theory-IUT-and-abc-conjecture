# S1201: fLinkAt 1 0 1 1 isoMon nontriviality and S1187 refl possibility

Date: 2026-10-30. Report only.

## 1. Search result

In `LeanFormal/IUT` the only `isoMon` facts for `I.fLinkAt` are in
`SourceH1H2Construction.lean` (:203-267):

- `fLinkAt_isoMon_bijective`: `Function.Bijective ((I.fLinkAt n m n' m').isoMon v)`;
- compatibility with unit/action/strip data.

There is no theorem:

```text
I.fLinkAt 1 0 1 1 |>.isoMon v ≠ MulEquiv.refl
```

nor a nonzero/unequal-unit witness, nor a quotient-level nontriviality
`TimesMuQuotient (Mon v)^x` statement.  In particular a link between different
lattice points is not proved nontrivial merely because the points differ:
`fLinkAt` is an actual `FPrimeStripEquiv`, but all current theorems are
bijectivity and compatibility, not non-identity.

## 2. Exact nontriviality statement still missing

Two possible exact targets:

```lean
def IsoMonNontrivial : Prop :=
  ∃ v : V, (I.fLinkAt 1 0 1 1).isoMon v ≠ MulEquiv.refl ((S10.Mon v)ˣ)
```

or the quotient-level form needed by the Kummer layer:

```lean
def KummerQuotientNontrivial : Prop :=
  ∃ v x : TimesMuQuotient ((S10.Mon v)ˣ),
    (S1187.kummerIsoAt (I.fLinkAt 1 0 1 1) v).equiv x ≠ x
```

The second is the correct condition for the `x mu`-Kummer isomorphism to be
non-refl, because the layer stores the quotient equivalence, not the unit
equivalence itself.

No existing theorem supplies either.

## 3. Is S1187 Kummer possibly refl?

S1187NonReflKummerCommonGroupActual:

```lean
kummerIsoAt φ v : TimesMuKummer.Isomorphism
  ((upper.unitsAction v).comp factorUpper)
  ((lower.unitsAction v).comp factorLower φ)
equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
```

Let `Qφv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))`.

### (a) As a quotient equivalence

`Qφv = MulEquiv.refl` iff `Units.mapEquiv (φ.isoMon v) = refl` iff
`φ.isoMon v = MulEquiv.refl ((upper.Mon v)ˣ)`, because `Units.mapEquiv` and
`quotientUnitsEquiv` are injective on MulEquivs.

Therefore the Kummer **equiv** is identity exactly when the strip equivalence
has identity unit component at every v.

### (b) As an `Isomorphism.refl`

`TimesMuKummer.Isomorphism.refl` has the form `Isomorphism rho rho` for a
single action `rho`.  For the S1187 layer:

- if `upper = lower` and `factorUpper = factorLower φ` and the actions agree,
  then `kummer` can be `refl` exactly when `Qφv = refl` for all v;
- for `upper = S10`, `lower = S11` (S1195), the source and target actions are
  on different strip unit groups, so `kummer` is not literally
  `Isomorphism.refl`; only its `equiv` can be the identity map.

In particular S1187's name `nonreflKummerLayer` is conditional: it is
non-refl only if `φ.isoMon` (or its quotient) is nontrivial.  For
`φ = I.fLinkAt 1 0 1 1`, this is exactly the missing theorem above.

## 4. Consequence for S1195/S1196

`S1195ActualUpperEnv` compiles EXIT=0 and constructs

```lean
upperEnv := sourceEvaluationArrowOfUnitPortion
  (I.fLinkAt 1 0 1 1) upperEnvUnit
upperEnvUnit := SourceEvaluationUnitPortion.ofKummerLayer
  (nonreflKummerLayer (I.fLinkAt 1 0 1 1))
```

but it does not prove `upperEnvUnit` is non-identity.  Therefore it cannot
claim the paper's nontrivial evaluation/Kummer content; it remains actual
conditional on the missing nontriviality.

`S1196NonReflSquare` currently fails at lines 39/45 because the upper/lower
orientation of `nonreflUpperEnv` does not match `ofThreeLegs` (S00/S01 vs
S10/S11); this is separate from nontriviality.

## 5. Conclusion

- actual: `fLinkAt.isoMon` is bijective and compatible; S1187 lifted layer
  compiles; S1195 upperEnv compiles.
- exact missing: `I.fLinkAt 1 0 1 1.isoMon` nontriviality, equivalently
  `KummerQuotientNontrivial` for the lifted `kummerIsoAt`.
- S1187 Kummer can equal identity/refl exactly when `φ.isoMon` has identity
  unit component (and actions coincide for literal refl).  This is not ruled
  out for `I.fLinkAt 1 0 1 1`.
- No new Lean written; EXIT=0 report.
