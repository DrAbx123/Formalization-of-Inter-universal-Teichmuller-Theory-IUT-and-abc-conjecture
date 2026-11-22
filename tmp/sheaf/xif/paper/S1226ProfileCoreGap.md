# S1226: Profile on I.family.index — exact first gap

Target:

```lean
Profile (Core (ℤ × ℤ) I.family.index)
```

with

```text
logVolume i := (I.family.theater i).thetaPacket.logVolume
possibleImage i := <thetaPacket corresponding set>
```

## Read

- `MultiradialOutputKernel.Core`: fields `base`, `level`, `ind1/ind2/ind3`,
  plus 15 axioms (zero/add/inverse, commutation, level).
- `FiniteThetaPacket`: fields `q`, `q_pos`, `scale`, `scale_eq`.
  Its `logVolume : Real` is the sum of `log(scale j)`; **it has no
  `possibleImage` field**.
- `OriginalInput`: has `family.index`, `index_equiv : family.index ≃ ℤ × ℤ`,
  `fPrimeStripAt`, and links `fLinkAt`, but **no Core/procession operations**.

## Actual parts

1. `stripOfChoice` (S1225) is actual:
   `stripOfChoice i = I.fPrimeStripAt (I.index_equiv i).1 (I.index_equiv i).2`.
2. `(I.family.theater i).thetaPacket.logVolume` is actual for every `i`.
3. `I.linkAt_q`/`I.linkAt_scale` show the theta packets of linked theaters agree,
   so `thetaPacket.logVolume` is actually independent of the theater index.

## First exact missing fields

### 1. actual Core operations

`Core.ind1`, `Core.ind2`, `Core.ind3`, `Core.level` on
`Choice := I.family.index` are not constructed by the source input.  The
lattice shifts through `I.index_equiv` are available as an index action, but
they are not the source procession operations; using them would silently
replace the paper's `(Ind1)/(Ind2)/(Ind3)` operations.

### 2. actual possibleImage set

`FiniteThetaPacket` supplies `logVolume` only.  The target `possibleImage`
set is not a field of the theta packet nor of `OriginalInput`; the closest
actual objects are the per-`j` values `thetaPacket.scale j : ℝ`, not a set of
allowed log-volumes.

Thus no `Profile` inhabitant is produced.  The first failing object is
`Core Label I.family.index`, before any Profile law.

## Exact minimum

```text
sourceCore : Core Label I.family.index
  -- with ind1/ind2/ind3 actual source procession operations
  -- and level actual
thetaPossibleImage : I.family.index → Set Real
  -- actual allowed-image set from the theta packet
```

Then `Profile` fields are:

```text
logVolume i := (I.family.theater i).thetaPacket.logVolume
possibleImage := thetaPossibleImage
```

and the four laws reduce to `thetaPacket.logVolume` invariance under the
source operations plus set containment for `ind3`.

Status: exact stop; no weak Core/Profile written.
