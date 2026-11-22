# IUT critique → Lean route audit (Scholze–Stix / LANA / ETA-8)

- date: 2026-10-24
- scope: map the Scholze–Stix and LANA critique points to the current Lean
  route, state which steps must be forbidden, which eta/log-shell donors are
  production-supported, which are exact gaps, and give the next executable
  package list.
- Lean changes: **none**. Audit document only.

Sources consulted: `coord/IUT-ROUTE-ETA.md`, `AUDIT_LEDGER.md` (LANA and
route entries), production log-shell/Kummer modules, and
`tmp/sheaf/n8/closure/P6RelaxedSemanticAudit.md`.

## 1. Critique points and their Lean counterparts

| Critique point | Lean counter-route that must be forbidden | Why |
|---|---|---|
| Direct comparison of abstract/data pilots across the Theta-link | Any proof of `Q <= Theta` / paper N8 from `P6Comparison`, `C9QThetaValuesNamed`, `P6RelaxedSourceRouteIntegration`, or a direct C4/C5 output-to-hull scalar map | The abstract/concrete pilots are not identified by production data; a direct scalar comparison reuses the criticized identification. |
| Trivializing all real lines to a common `R`, then demanding commutativity | Any use of `Real` as a shared ambient line for q, theta, hull and log-shell values without separate unit/log-shell integral data | The paper keeps distinct copies/constructions; a common `R` erases scaling and monodromy. |
| Identifying copies of `R` without preserving construction/scaling | Any direct equality of `qPilotSignedLog` with `sourceHullVolume`/hull outputs or `P6Readout.value` | Identification must go through an actual construction map, not equality of Real numbers. |
| `O(l^2)`/monodromy factors and noncommuting hexagon | Any derivation of Cor.3.12/N8/C9 through the Scholze–Stix hexagon or through a direct diagram commutativity field | LANA confirms the hexagon does not commute; a direct diagram proof requires the missing factor. |
| LANA: eta-algorithm alternative | n/a (this is the allowed route) | Compare `eta^q` and `eta^anab_S` before degrees/volumes. |

## 2. Steps that must be forbidden in the Lean route

1. **Direct-pilot comparison.** No theorem of the form
   `Q <= Theta` or `qPilotSignedLog = hullVolume` from
   `P6Comparison`, `C9QThetaValuesNamed`, `P6RelaxedGlobalNumerical`,
   `P6RelaxedSourceRouteIntegration`, or a direct `C4`/`C5` output map.
2. **Common-real-line collapse.** No `Rval = Rss = Real` identification and no
   common `Real` container reused for q-pilot, theta, log-shell and degree
   values.
3. **Direct degree/hull step.** No degree comparison, hull containment or
   normalized-log-volume inequality before `eta^q = eta^anab_S` is proved.
   In particular, forbidding the old `hull_bound`, `qPilot_mem_hull`,
   `degree_preserved` and `Q_le_hull` routes as source theorem.
4. **Degenerate readout.** No `reference = region` readout, no `Theta = 0`,
   no `Values = {0}`, no `JRange = Set.univ` target; see
   `P6RelaxedSemanticAudit.md`.
5. **Free Real adjustments.** No `Ind1/2/3` encoded as free Real offsets or
   arbitrary common-line adjustments; they must be part of an admissible
   integral structure/construction.
6. **Axiom or arbitrary donor substitution.** No imported “LANA-proved” or
   “IUT-proved” theorem, no arbitrary carrier, no `True`/empty interface.

## 3. Production-supported eta/log-shell donors

These are actual production modules, but they are **donors**, not yet an eta
construction:

- `LeanFormal/IUT/Foundations/LocalFields/IntegralLogShell*` — integral
  log-shell, index/volume/scaling/frobenius layers.
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/LogShellVolume*`,
  `LogShellVolumeConsumer`, `LogShellSaturation*` — actual log-shell volume and
  saturation consumers.
- `LeanFormal/IUT/IUTII/Kummer/SourceLogShell*` —
  `sourceLocalLogShellDatum`, kernel/image/log-shell carriers and action
  compatibility.
- `LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean`,
  `SourceLogShellCarrier.lean`, `SourceLogShellQuotient*` — source local
  log-shell data used by C2.
- `LeanFormal/IUT/IUTII/Frobenioid/Example36LogShellLattice.lean`,
  `Example36LogShellFrobeniusAction.lean` — lattice and Frobenius actions.
- Native q/Tate donors: `Example36TateUniformization`,
  `TateCoordinateNormalization`, `TateUniformizationPointMap`,
  `SourceImageHull` (`sourceThetaPilotPoint`, hull/volume), native C1/C3
  actual slices.
- P6 actual readout/Adm donors: finite/adm/arch modules — useful only after
  the degenerate reference=region issue is corrected.

## 4. Exact gaps

| Gap | Status in current tree |
|---|---|
| `Rval`: actual value-group real line from native q/selected places | No production declaration; only `Real` and scattered value monoids. |
| `Rss`: real line from log-shells/volume containers | Log-shell carriers exist, but no actual map to a common `Rss`. |
| `EtaQ : Rval -> Rss` actual q-pilot construction | No production `EtaQ` declaration. |
| `EtaAnab S : Rval -> Rss` actual Kummer/log-shell construction | No production `EtaAnab`; requires chosen integral structure S. |
| `EtaComparison : EtaQ = EtaAnab S` | Open named gap; no proof, no counterexample decided. |
| Common volume container after eta equality | Absent. |
| Nonzero `Theta`/Values from eta route | Absent; all current actual relaxed readouts are zero (audit). |
| Actual `Q <= Theta` after eta comparison | Absent; current destinations omit it or use trivial zero. |

## 5. Next executable package list

### ETA-8a: `SourceValRealLine` (actual Rval)

- Input: actual native `N8NativeInput` + C1 finite places + actual q/Tate
  data.
- Define an actual value-group real line from the pinned unit/value group,
  preserving log/sign and place data.
- Do not use bare `Real` as a shared line.
- Acceptance: `lake env lean` exit 0, no arbitrary carrier, exact type report.

### ETA-8b: `SourceSsRealLine` (actual Rss)

- Input: production `IntegralLogShell*` / `LogShellVolume*` /
  `SourceLogShell*` carriers.
- Define the log-shell/volume-container real line with integral structure and
  filtration preserved.
- Acceptance: exit 0, actual log-shell dependency matrix recorded.

### ETA-8c: `EtaQConstruction`

- Construct `EtaQ : Rval -> Rss` from native q-pilot/Tate data only.
- Must not use hull/degree values.
- Named gaps allowed only for missing production bridge declarations; no
  free Real adjustment.

### ETA-8d: `EtaAnabConstruction`

- Construct `EtaAnab S : Rval -> Rss` from Kummer/log-shell + chosen
  integral structure S.
- S must be an actual source object, not an arbitrary field.
- Ind1/2/3 must be encoded in S/construction, not free Real offsets.

### ETA-8e: `EtaComparison`

- State and attempt `EtaQ = EtaAnab S` for suitable S.
- If actual proof exists, accept; otherwise file exact named gap or decisive
  no-go with the missing production declaration.
- No direct hexagon/commutativity assumption.

### ETA-8f: post-eta volume/comparison

- Only after ETA-8e: build the common volume container and normalized
  log-volume comparison.
- Derive `Q <= Theta` only from the eta comparison and actual same-side
  construction, never from a scalar sign or a common Real line.
- Keep `Theta != 0`/nondegenerate Values as an explicit target condition and
  reject any `reference = region` readout.

## 6. Routing decision

- The old frozen/relaxed direct-readout paths are **negative controls only**;
  they must not be presented as paper N8/C9/C10 closure.
- The active route is ETA-8: actual `Rval`, actual `Rss`, actual `EtaQ`,
  actual `EtaAnab S`, then `EtaComparison`.
- No theorem at any stage may be accepted from an external paper, LANA CI
  record, or a route label alone.

## Status

- statement_compiles: not applicable (audit only).
- proof_body_checked: not applicable.
- kernel_closed: not applicable.
- target_accepted: no; ETA-8 route is a next-package plan, not a proof.
- Lean files changed: none.
