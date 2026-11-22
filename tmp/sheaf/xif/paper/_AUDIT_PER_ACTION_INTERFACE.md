# Per-action G2 interface — audit record

Date: 2026-11-10 (Asia/Shanghai)

## Claim

The per-action interface is kernel-closed with no extra axioms: all five key
theorems depend only on `[propext, Classical.choice, Quot.sound]`. No fake
unconditional theorem was added; the per-action theorem assumes the raw `hfac`
(the remaining qside provider).

## Artifacts

- `S3127G2UniversalDataOfHfacActual.lean` — 2518 B
- `S3127G2RawLiftInterfaceActual.lean` — 4029 B
- `S3127FreeQuotientExistsOfFreeActionActual.lean` — 2581 B
- `S3127FreeQuotientExistsOfFreeActionConsumerActual.lean` — 3257 B
- `S3127G2UniversalTargetActual.lean` — 1975 B

## Axiom probe

Probe: `_S3127PerActionInterfaceAuditProbe.lean` (EXIT0).

```
'...S3127G2UniversalData_of_hfac' depends on axioms: [propext, Classical.choice, Quot.sound]
'...S3127G2UniversalData_of_rawLiftData' depends on axioms: [propext, Classical.choice, Quot.sound]
'...S3127FreeQuotientExists_ofFreeAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'...S3127FreeQuotientTargetOf_universal_of_hfac' depends on axioms: [propext, Classical.choice, Quot.sound]
'...S3127G2QuotientUniversalOf' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Remaining dependency

`hfac`: for every invariant map, the raw lift exists, factors, and is unique.
Provider owned by qside (`UniversalDataOfLiftFull` / raw fac + uniq).
Once supplied, `S3127FreeQuotientExists_ofFreeAction` is unconditional for
given `act`, `hfree`, `hInv`.

## Not claimed

- No unconditional `S3127FreeQuotientExists` (global `∀ G A` form).
- No `sorry`/new axiom; global `PaperInput` remains documentation only.