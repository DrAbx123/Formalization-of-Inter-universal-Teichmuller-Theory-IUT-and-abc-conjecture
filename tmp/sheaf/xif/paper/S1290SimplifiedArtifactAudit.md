# S1290: simplified-artifact audit before original-object work

Rule: simplified objects may be retained as scaffolding or conditional
reductions, but must NOT be counted as constructions of the paper objects or
used for final judgment.  Original-object priorities:
SourceDefinition31Data D5-D11; SourceProcessionCapsuleContract actual integral
log-shell/polyIso; KappaOrbitUnitsActionPairDatum nontrivial kappa; C3
completion roots/action; true HDD hull+det module; theta line
bundle/function/divisor.

## A. Products from this line that are simplified / not paper objects

| file | what it actually is | verdict |
|---|---|---|
| `S1225SourceStripOfChoiceActual.lean` | `stripOfChoice : I.family.index -> FPrimeStrip` via `fPrimeStripAt o index_equiv` | actual source-index map, but **not** `ProcessionChoice` and not the algorithm input choice; do not use as SourceRun/choice bridge |
| `S1187NonReflKummerCommonGroupActual.lean` | actual `TimesMuKummer.Isomorphism` from `FPrimeStripEquiv.isoMon` on graph group | actual reduced link Kummer, but not the C3 completion/Kummer root action; not the paper's vertical Kummer isomorphism |
| `S1195ActualUpperEnv.lean` | `upperEnv` from S1187 layer + `fLinkAt 1 0 1 1` | reduced upperEnv; provenance is generic `fLinkAt`, not the construction algorithm evaluation; not paper evaluation |
| `S1200NonReflKummerSquareActual.lean` | attempted same-G square | did not compile (G/topology mismatch); do not count |
| `S1210NoRootWitnessActual.lean` | `noPaperQRootCard` from S342 | actual F-side negative; does not decide K-side root; not a K-side construction |
| `S1272KSideRootGap.md` / `S1284KOrderControlActual.lean` | K-side root/order gap reduction; actual arithmetic equivalence `(2l)|order_K <-> l|e and 2|order_K` | exact reduction only; `l|e`, `2|order_K`, root valuation still unproved |
| `S1133PaperLVExGluingActual.lean` | scalar gluing attempt using S914 simplified R/S logs | did not compile; do not count |
| `S1150SourceRunAudit.md`, `S1156/S1163` reports | early SourceRun/upperEnv designs | audit only; weak `SourceRun` skeletons deleted/not queued |
| `S1226ProfileCoreGap.md` | Core/Profile gap | no Profile constructed; index-shift Core was rejected |
| `S1262HDDLocalLatticeActual.lean` | rank=1 HDD local lattice = span of the actual unit-section localization in the completed local field | **simplified HDD lattice**; the paper HDD needs the actual hull + determinant module, not rank=1 unit-section span |
| `S1287SourceHDDReadoutAssemblyActual.lean` | packages S1262 lattice + S1275 SHE localization + actualSHEOutput readout | actual fields, but built on the simplified rank=1 HDD lattice; not dsc->paper hull+det |
| `S1215SourceSHEHDDCompatibilityActual.lean` / `SHEOutputActual.oneColumnStructure` | one-column structure over completed Q rings, rank-1 integral line bundle, actualSHEOutput localizations | actual one-column readout donor, but the paper arithmetic vector bundle is rank >1 (IUT III xi-d); not the paper HDD module |
| `S1275SHEDDNonLatticeFieldsActual.lean` | actual sheLocalization/readout from actualSHEOutput | actual at the simplified one-column/rank-1 level; localizeSection stays exact; not paper HDD hull/det |
| `S1282SourceLevelActual.lean` | `sourceLevel i := (I.index_equiv i).1.toNat` | actual index-coordinate Nat; not the paper Core level, and not additive on all Int; use only as source-index scaffold |
| `S1270NontrivialCapsuleActual.lean` | IQSpan of actualLocalLogShellDatum, with actualIQSpan_eq_span_integralLogShell | retains integral log-shell span on this instance, but still the reduced capsule shell, not SourceProcessionCapsuleContract actual polyIso |

## B. Existing artifacts explicitly classified as simplified

| object | why it is not the paper object |
|---|---|
| `ConcreteFiniteTheorem311.ProcessionChoice` / `SourceFiniteParameterized.carrier` / `finiteKernelProcessionAutomorphism` / `finiteKernelInd2ActionData` / `finiteKernelRun` | finite test carrier; `Choice` is the finite procession model, not the paper source choice; finiteKernelRun is not the paper source run |
| `SourceOutputPrimeStripInterpretation.SourceRun` on arbitrary `Carrier Label Choice` | actual reduced algorithm record, but no source `Choice -> strip` and no source evaluation; not the paper SourceRun |
| `S1226` Core via index coordinate shifts | rejected; `level := 0` / coordinate shifts are not source Ind actions |
| `IPLAPTDataActual.selfKummerLayer` / `selfEvaluationUnitPortion` | refl/self-conjugate Kummer layer, not a nontrivial source Kummer action |
| `S459KrootCandidateActual.candidateKRoot` | root only in `AlgebraicClosure (Completion ...)`, not in the completion; algebraic-closure root is not a C3 completion root |
| `PaperCompletionThetaValueActual` | marked INVALID AS PAPER OBJECT; 2l-root card impossible by S342 |
| `S342` F-side `QParameterTwoLRootCard` | impossible; cannot be used as C3/K-side root |
| `SourceLogShellIQTensorPacket` IQSpan/Q-vector packets | reduced Q-span/tensor models; if integral/Z_p structure is needed they are not the actual integral log-shell |
| `SourceLogShellXMuPacket` chain supply | reduced Q-linear chain; no integral/Z_p log-shell |
| `ThetaFunctionLineBundleActual.ActualQThetaValueData` | real-unit theta values, not theta line bundle/function/divisor |

## C. Retain as actual (not paper-object substitutes)

- S1284 `twoL_dvd_order_K_iff_ramification_and_two`: actual arithmetic reduction;
  keeps `l|e` and `2|order_K` as exact open inputs;
- S1210 `noPaperQRootCard`: actual F-side impossibility;
- S1187/S1195: actual reduced Kummer/evaluation arrows, useful only under the
  reduced-link semantics; must not be quoted as paper C3/evaluation;
- S1225 `stripOfChoice`: actual map on `I.family.index`; useful as a source-
  index scaffold, not as `ProcessionChoice`/SourceRun.

## D. Original-object next targets (not to be replaced)

1. `SourceDefinition31Data` D5-D11 actual fields (no finite-model substitute).
2. `SourceProcessionCapsuleContract`: actual integral log-shell/polyIso.
3. `KappaOrbitUnitsActionPairDatum` with nontrivial `kappaUpper/kappaLower`
   (not self/refl/conjugated refl).
4. C3 completion roots/action (K-side; not algebraic-closure root; not F-side
   impossible card).
5. true HDD hull + determinant module (not `rank=1` unit-section toy).
6. theta line bundle/function/divisor (not `ActualQThetaValueData` real units).

## E. Decision

Do not use A/B objects for final judgment.  The next accepted package must
construct one of D1-D6 or stop at its first exact field, with a named consumer.
