# S1211: attempt at isoMon nontriviality for I.fLinkAt 1 0 1 1

Date: 2026-10-30. Report only; no wrapper.

## 1. Actual data for fLinkAt

`SourceOriginalInput.linkAt` (SourceOriginalInput.lean:60) is the field

```lean
I.family.link (I.indexOf n m) (I.indexOf n' m')
```

and `SourceHodgeTheaterFamily.link` (SourceHodgeTheaterFamily.lean:37) is an
arbitrary field

```lean
link : ∀ i j, HodgeTheaterLink (theater i) (theater j)
```

with only laws `link_refl`, `link_trans`, plus q/scale compatibility.  There is
no formula for `linkAt` at distinct indices, and in particular no formula for
`HodgeTheaterLink.primeStripEquiv.isoMon`.

`SourceH1H2Construction.fLinkAt` is:

```lean
I.fLinkAt n m n' m' = (I.linkAt n m n' m').primeStripEquiv
```

and `fLinkAt_eq` (H1H2:173) is definitional.  No nontriviality theorem exists.

## 2. Different lattice points

`OriginalInput.theaterAt_eq_iff` says different lattice points give different
Hodge theaters (`family.distinct`).  But a `HodgeTheaterLink` between distinct
theaters can have identity `isoMon`: distinctness is a property of the whole
Hodge-theater structure, not of the unit Mon component.  The link could differ
in `isoPi`, `isoG`, theta data, or actions while `isoMon` is refl.

No theorem states: `i ≠ j -> (family.link i j).primeStripEquiv.isoMon ≠ refl`.

## 3. Actual q_v unit

`qVFamily T b` lives in `Completion (qVPlace)` / its algebraic closure.
`TwoLthRootKummerActual.qVAlgClosedUnit` and `hodgeTwoLthRoot` are actual q_v
units/root data.

There is no theorem relating `qVFamily`/`qVAlgClosedUnit` to the unit monoid
`I.fPrimeStripAt n m).Mon v` or to `fLinkAt.isoMon`.  The q_v unit is not an
element of the strip unit groups, and no evaluation identification is present.
Hence q_v cannot witness `isoMon ≠ refl`.

## 4. What could have worked but does not

- `linkAt_refl` only gives identity at the same index; at `(1,0) ≠ (1,1)` it
  gives no information.
- `linkAt_trans` composes links; it does not force a factor to be non-refl.
- `compatDegree`/`compatAction` are compatibility laws; an identity isoMon
  satisfies them trivially.
- `theaterAt` distinctness does not imply `isoMon` nontrivial.

## 5. Exact missing witness

The minimal exact witness is one of:

```lean
def IsoMonNontrivial : Prop :=
  ∃ v : V, (I.fLinkAt 1 0 1 1).isoMon v ≠ MulEquiv.refl ((S10.Mon v)ˣ)
```

or, for the Kummer quotient layer:

```lean
def KummerQuotientNontrivial : Prop :=
  ∃ v x : TimesMuQuotient ((S10.Mon v)ˣ),
    (S1187NonReflKummerCommonGroupActual.kummerIsoAt
      (I.fLinkAt 1 0 1 1) v).equiv x ≠ x
```

No current source field supplies either.  A source construction would have to
identify the actual neighbor link with an explicit non-identity unit action
(e.g. a translation/multiplication by a nontrivial q_v unit) and prove the
compatibility; the `link` field alone is arbitrary.

## 6. S1187 Kummer refl possibility

S1187 compiles EXIT=0 and constructs

```lean
nonreflKummerLayer φ :
  SourceTimesMuKummerLayer (GraphGroup upper) upper lower
kummer v := kummerIsoAt φ v
kummerIsoAt φ v equiv := quotientUnitsEquiv (Units.mapEquiv (φ.isoMon v))
```

The `equiv` is identity iff `φ.isoMon v = refl` (because Units.mapEquiv and
quotientUnitsEquiv are injective on MulEquivs).  For literal
`TimesMuKummer.Isomorphism.refl`, source/target actions must also coincide; for
`upper = S10`, `lower = S11` they do not, so only the equiv can be identity.

Thus S1187's name `nonreflKummerLayer` is conditional: if
`I.fLinkAt 1 0 1 1.isoMon` is identity, the lifted layer is the identity
quotient layer (trivial Kummer content).  This is not ruled out.

S1195 compiles EXIT=0 but only supplies `upperEnv` conditional on this
nontriviality; S1196 currently fails at lines 39/45 due upper/lower orientation
(separate issue).

## 7. Conclusion

- No actual nontriviality witness for `I.fLinkAt 1 0 1 1.isoMon`.
- Different lattice points, family distinctness, and actual q_v units do not
  imply it; the link field is arbitrary and q_v is not in the strip unit group.
- Exact first gap: `IsoMonNontrivial` / `KummerQuotientNontrivial` above.
- S1187 Kummer can equal refl/identity if isoMon is identity; no theorem excludes
  this for `I.fLinkAt 1 0 1 1`.
- Report only, no Lean wrapper, EXIT=0.
