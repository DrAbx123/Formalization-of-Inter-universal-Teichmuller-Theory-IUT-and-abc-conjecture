# L1-F5 — Source log-Kummer identification (stage 1/2)

- Node: L1-F5
- Owner: logdescent
- Target production file: `LeanFormal/IUT/IUTII/Frobenioid/Example36SourceLogKummerIdentification.lean`
- Stage: 1/2 only. No production edit in this delivery.
- Actual consumer: `Example36SourceLogLinkCompatibility.lean` and the Project import of the target.
- Date: 2026-10-22

## 1. Frozen target and consumer

The target file must eventually inhabit

```lean
SourceFrobeniusLogKummerIdentificationCard l LogKummerMap.logKummerData
```

for the source local field `Q_l` and the tree log-Kummer data at the concrete
Gaussian place.  The card is defined in
`Example36LogKummerMap.lean:339`; its fields are:

- `SourcePrincipalUnits`, `sourceFrobenius`;
- `SourceLogShell`, `sourceLogKummer`, `sourcePScaling`;
- `carrierEquiv : SourcePrincipalUnits ≃ data.H`;
- `shellEquiv : SourceLogShell ≃ data.logShell`;
- `frobenius_intertwines`, `logKummer_intertwines`, `pScaling_intertwines`.

No inhabitant of this card exists in the target or in any production file
checked here.

Consumers found by import/reference search:

- `Example36SourceLogLinkCompatibility.lean` imports the target
  (`...`, line 7) and explicitly states that no continuous ring map
  `Q_l →+* concreteLogShellField` and no identification of the two log-Kummer
  carriers is constructed (header lines 49–62).  It proves only the maximal
  actual square along `PadicScalarField concretePlace →+* K_v`.
- `Project.lean:519` imports the target, so the target itself is in the
  production entry closure; the import is not a consumer of the missing card.
- `LogShellFrobeniusConsumerGeneral.lean` imports the target and consumes the
  log-shell/Frobenius side, not the identification card.
- `SourceQlCarrierMap.lean` and `SourceQlEmbeddingConsumer.lean` import the
  target and contain candidate analytic/transport statements (see §3).

## 2. Actual green inventory

### 2.1 Target file (green olean exists)

`Example36SourceLogKummerIdentification.lean` (373 lines; no `sorry`):

- `sourceLocalField l := ℚ_[l.value]`;
- `sourcePrincipalUnits l := principalUnits (K := ℚ_[l.value])`;
- `sourceLogKummer := principalUnitLog`;
- `sourceLogShell := principalUnitLogImage`;
- `sourceFrobenius u := u ^ l.value`;
- `sourcePScaling x := l.value * x`, with
  `sourceLogKummer_square`;
- `sourcePScaling_nontrivial` via the sharp inverse ball;
- `independentSourceFrobeniusLogKummerCard : SourceFrobeniusLogKummerCard l`
  (structural card only, not the identification card);
- Q5 field comparison `concretePlace_qFiveComparisonRingEquiv`, norm
  preservation, `concretePlace_integersRingEquiv`,
  `concretePlace_unitsEquiv`, `concretePlace_principalUnitsEquiv`.

### 2.2 Tree log-Kummer data (green olean exists)

`Example36LogKummerMap.lean`:

- `LogKummerMap.logKummer : principalUnits (K := concreteLogShellField) →
  principalUnitLogShell`, `unitLog`-based, surjective;
- `logKummerData : LogKummerData` with
  `H = principalUnits (K := concreteLogShellField)`,
  `logShell = principalUnitLogShell`;
- `treeSourceFrobeniusLogKummerCard` uses the **scaled** logarithm
  `scaledPrincipalUnitLog` into the **integral** log-shell, not `logKummerData`.

### 2.3 Analytic compatibility candidates (source-level, no olean checked)

`SourceQlCarrierMap.lean` and `SourceQlEmbeddingConsumer.lean` contain:

- `sourceQlEmbedding_principalUnitLog_compat`:
  `e (principalUnitLog u) = principalUnitLog (unit transport u)` for the
  isometric embedding `Q_l → F_v`;
- `sourceQlEmbeddingLogShellMap : sourceLogShell l →+
  principalUnitLogImage (K := CommonPrimeCompletion place) l.value`;
- `sourceQlEmbedding_scalingSquare`: source `l.value`-scaling is carried to
  target `p`-scaling at `p = l.value`.

Both files are no-sorry candidates; no `.olean` was found under
`.lake/build/lib/lean` in this session, so they are **not proof-body-checked**.
They are the right proof base for F5-a/F5-b but must be built before use.

## 3. Exact gap decomposition

### F5-a (minimal next node) — concrete shell map from Q_l

For `place := concretePlace` and `l.value = 5`, expose the existing additive
embedding on the actual concrete field:

```lean
noncomputable def sourceQlLogShellMapConcrete :
    sourceLogShell l →+ LogKummerMap.logKummerData.logShell
```

with the pointwise generator rule

```lean
theorem sourceQlLogShellMapConcrete_logKummerShell
    (u : sourcePrincipalUnits l) :
    sourceQlLogShellMapConcrete (sourceLogKummerShell l u) =
      LogKummerMap.logKummer
        (sourceQlEmbeddingUnitMap l concretePlace
          (u : (Integers (sourceLocalField l))ˣ)) := ...
```

The proof should be a transport of
`sourceQlEmbeddingLogShellMap` + `sourceQlEmbedding_principalUnitLog_compat`
along the definitional equality `CommonPrimeCompletion concretePlace =
NormalizedCompletion concretePlace = concreteLogShellField` (the last equality is
`Example36LogShellLattice.lean:94`).  This is the analytic compatibility missing
from the target's own Q5 section; it should not be re-proved from scratch.

### F5-b — bijective carrier/shell equivalences at l = 5

The card needs equivalences, while the Q_l embedding is only isometric/injective.
At `concretePlace`, the completion degree over the lower Q5-completion is one
(`Example36SourceLogKummerIdentification.lean:232`,
`concretePlace_completion_finrank_eq_one`), and
`concretePlace_principalUnitsEquiv` is already constructed.  The next node is
to identify the source Q_l principal units/shell with the concrete ones through
that equivalence, and then package F5-a into
`SourceFrobeniusLogKummerIdentificationCard` for `l.value = 5`.

### F5-c — scaled/unscaled intertwiners

The target card is stated against `LogKummerMap.logKummerData`, which is
**unscaled** (`principalUnitLogShell`, `logKummer`).  The tree structural card
`treeSourceFrobeniusLogKummerCard` is **scaled**
(`scaledPrincipalUnitLog`, `integralLogShell`, factor
`(logShellScale p)⁻¹`).  Those are different data packages.

Exact missing comparison, if the scaled tree card is to be matched:

```lean
scaledPrincipalUnitLog u =
  (logShellScale concreteRationalPrime : concreteLogShellField)⁻¹ •
    LogKummerMap.logKummer u
```

(upto the subtype/wrapper difference between `integralLogShell` and
`principalUnitLogShell`).  The source Q_l `sourcePScaling` is unscaled
multiplication by `l.value`; its image under F5-a is unscaled target
multiplication by 5, whereas the tree scaled card uses `integralLogShellPScaling`.
No theorem in the target bridges these two packages.

### F5-d — general l place-model mismatch

`sourceLocalField l = ℚ_[l.value]` but the concrete place lies over 5 in the
Gaussian field.  For `l.value ≠ 5` there is no continuous ring map
`ℚ_[l] → concreteLogShellField` from the source data; the target itself records
this obstruction (`sourceComparison_obstruction`, lines 196–204) and the
log-link compatibility file states it explicitly.  A card for all
`l : PrimeGeFive` cannot be inhabited by the concrete Gaussian model; only the
`l.value = 5` special case is on the present consumer path.

### F5-e — perfection (separate; not on the card path)

`SourceUnitPerfection place = UnitLogPerfection (SourceAlgebraicClosure place)`
with `sourceUnitPerfectionEquiv : SourceUnitPerfection place ≃ₗ[ℚ]
SourceAlgebraicClosure place` (`ABCBridge/Geometry/
FinitePlaceSourceAlgebraicUnitPerfection.lean:22–27`).  The target card only
requires principal units and the log-shell, not unit perfection.  The perfection
object lives on the algebraic closure, while the source Q_l construction lives on
principal units of `ℚ_[l]`; no theorem checked here produces a map from
perfection to those principal units or their log-shell.  This is a separate node
(`F5-e`) and must not be silently used as a field of the card.

## 4. Child nodes and order

1. `F5-a` — concrete `sourceQlLogShellMapConcrete` + generator compatibility
   (stage 3 candidate; first Lean file).
2. `F5-b` — principal-unit/shell equivalences at `l.value = 5` via the
   completion-degree-one `concretePlace_principalUnitsEquiv`.
3. `F5-card` — inhabit
   `SourceFrobeniusLogKummerIdentificationCard l LogKummerMap.logKummerData`
   for `l.value = 5`; the parent L1-F5 remains open for general `l`.
4. `F5-c` — scaled/unscaled comparison, only if a consumer actually asks for
   the scaled `treeSourceFrobeniusLogKummerCard`; do not add it to the unscaled
   card.
5. `F5-e` — perfection bridge; independent and currently without a target
   consumer on the card path.

## 5. Stage status

- `statement_compiles`: no new Lean statement compiled in this stage-1/2 note.
- `proof_body_checked`: target file has an olean and no `sorry`; Q_l candidate
  files have no olean and were not proof-body-checked.
- `kernel_closed`: no.
- `target_accepted`: no.
- Production files changed: none.

## 6. Minimal next executable step

Build the two Q_l candidate modules, then add `F5-a` as a thin wrapper in a
new node file (not in the target owner file yet):

```lean
noncomputable def sourceQlLogShellMapConcrete ...
```

and prove its generator compatibility by transporting
`sourceQlEmbeddingLogShellMap` and
`sourceQlEmbedding_principalUnitLog_compat`.  This tests the actual
`CommonPrimeCompletion concretePlace = concreteLogShellField` identification
before attempting the card.
