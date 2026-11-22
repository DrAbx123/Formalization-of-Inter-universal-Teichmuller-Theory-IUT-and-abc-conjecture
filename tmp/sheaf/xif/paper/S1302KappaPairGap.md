# S1302: KappaOrbitUnitsActionPairDatum — exact first field

Target: an actual pair datum with nontrivial `kappaUpper/kappaLower`, from
actual source units/action/factorization + Kummer root data.  Self-conjugate/
refl layers and finite models are excluded.

## Structure (existing)

`KappaOrbitUnitsActionPairDatum G upper lower` has fields:

```text
sourceUnits : V → Type
[CommGroup (sourceUnits v)]
sourceAction : ∀ v, G →* MulAut (sourceUnits v)
factorUpper : ∀ v, G →* upper.Pi v
factorLower : ∀ v, G →* lower.Pi v
kappaUpper : ∀ v, TimesMuKummer.Isomorphism (sourceAction v)
  ((upper.unitsAction v).comp (factorUpper v))
kappaLower : ∀ v, TimesMuKummer.Isomorphism (sourceAction v)
  ((lower.unitsAction v).comp (factorLower v))
```

`layerKummer D v := kappaUpper.symm.trans kappaLower`.

## Actual ingredients available

- upper/lower actual strips `I.fPrimeStripAt 1 0` / `I.fPrimeStripAt 1 1`;
- actual `φ = I.fLinkAt 1 0 1 1 : FPrimeStripEquiv upper lower`;
- actual factors on `G := (v : V) → upper.Pi v`:
  `factorUpper = Pi.evalMonoidHom`, `factorLower = isoPi ∘ eval`;
- actual non-refl `TimesMuKummer.Isomorphism`
  `S1187.kummerIsoAt φ v :
    Isomorphism (upper.unitsAction v ∘ eval)
      (lower.unitsAction v ∘ isoPi ∘ eval)`;
- actual `layerKummer` shape from the pair datum is available once the
  source units/action are supplied.

## First exact field: sourceUnits/sourceAction

The missing actual object is the source group-theoretic module

```text
sourceUnits : V → Type
sourceAction : ∀ v, G →* MulAut (sourceUnits v)
```

of IUT II Definition 4.9(i).  The tree supplies only strip unit groups
`(upper.Mon v)ˣ`, `(lower.Mon v)ˣ`; it does not supply the source
`O^x(G)` module/action.

If one substitutes `sourceUnits := (upper.Mon v)ˣ` and
`sourceAction := upper.unitsAction ∘ factorUpper`, then `factorUpper = eval`
forces `kappaUpper = Isomorphism.refl`; this is exactly the forbidden
self/refl substitution.  The same happens symmetrically on the lower side.

The actual non-refl S1187 isomorphism can only serve as `kappaLower` under
that refl-side substitution; it does not produce a genuine pair datum with both
kappa's from the source module.

## Second exact field: nontriviality witness

Even with a pair datum built from the strip unit module, one still needs

```text
(v : V) (x : TimesMuQuotient (sourceUnits v))
(kappaUpper/kappaLower).equiv x ≠ x
```
with actual Kummer root/unit provenance.  S1210 records this witness as
absent; the q_v 2l-root route is blocked by S342.

## Consumers

```text
KappaOrbitUnitsActionPairDatum
  → layerKummer : SourceTimesMuKummerLayer
  → non-refl vertical Kummer/evaluation data
  → upperEnv/square / IPL algorithmic provenance.
```

## Exact minimum

```text
sourceUnits / sourceAction (actual O^x(G) module/action)
+ kappaUpper / kappaLower (actual nontrivial Ism representatives)
+ nontriviality witness from actual Kummer root data.
```

Status: exact stop at `sourceUnits`; no self/refl pair datum, no finite-model
substitute, no weak Lean file.
