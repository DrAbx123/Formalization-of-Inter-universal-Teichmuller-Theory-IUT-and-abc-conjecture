# Paper objects vs existing repo (Cor312/StepXI)

## 1. Alignment table

| Paper object | Existing repo definition | Status |
|---|---|---|
| Initial Theta data / source quantifiers | `Theorem311Source.OriginalInput`; `SourceNativeInitialThetaData` | actual source fields |
| Theta special values q_v^(j^2) | `FiniteThetaPacket` (`q : Real`, `scale j = q^(j^2)`) | real-valued Gaussian abstraction; NOT actual p-adic q_v^(j^2) |
| Theta-pilot processions | `ThetaPilotCarrier = Fin (lStar+1)` | actual finite carrier |
| Theta-pilot image points | `ThetaPilotPoint`, `sourceThetaPilotPoint`, `possibleThetaPilotImageSet` | value-monoid realization; actual |
| Union of possible images | `possibleThetaPilotImageSet` | value-level; no Ind1/2/3, no Kummer action |
| Holomorphic hull | `sourceHolomorphicHull` (least candidate hull) | value-monoid hull; NOT literal IQ lambda-O hull |
| Literal lambda-O / IQ hull | `IsLambdaOHull`, `LiteralArithmeticHullInterface` | interface exists; `literalHullInterface_impossible` proves the value abstraction cannot supply it |
| Hull Haar/log-volume | `SourceUnitRegionHaarData`, `sourceSetVolume`, `sourceUnitRegionHaarInterface` | conditional Haar data; not literal IQ Haar |
| q-side value | `sourceQSideNormalizedValue`, `sourceSetVolume_possibleImage_eq_iSup_sourceQSide` | value-level q comparison; paper-faithful signed q carrier missing |
| Step XI final contract | `StepXIContract`, `CardQCMPComparison`, `CertificateHullWiring`, `IQHullLogVolumeInterface` | conditional final wiring; source construction unfinished (`Contract.lean` audit note) |
| Ind1/Ind2/Ind3 | StepXI/Ind files, `SHE`, `APT`, `IPL` | named obligations / conditional evidence; not actual actions on a literal packet |
| Procession normalization | `SourceProcessionStepXI`, `SourceProcessionStepXIMinimalForm` | source-level procession data; conditional |
| Completion 2l-th root | `TwoLthRootQVActual`, `TwoLRootExistenceGap` | exact missing; Q_5 counterexample |

## 2. Exact gaps found in repo

### G1. Literal IQ carrier / log-shell / Haar hull
`SourceImageHull.lean` states: the paper's lambda-O hulls live in the
inductive-system carrier `IQ(S±; n,°D^⊢)` with log-shell and Haar log-volume;
these are not fields of `OriginalInput`.  `LiteralArithmeticHullInterface`
is contradictory at this abstraction (`literalHullInterface_impossible`).
So the repo's value-monoid hull is provably not the literal paper hull.

### G2. Actual theta packet
`FiniteThetaPacket` is a real Gaussian packet `q^(j^2)`, not the actual
`q_v^(j^2)` in `K_v`.  No completion root exists (`TwoLRootExistenceGap`;
`padic_five_no_twoL_root`).  This is the root/kernel gap.

### G3. Ind1/Ind2/Ind3 actions
The repo has StepXI obligation/contract files, but no actual Ind actions on a
literal arithmetic packet.  At the value level, `possibleThetaPilotImageSet`
uses only labels, not the three indeterminacies.

### G4. q-side signed carrier
`sourceQSideNormalizedValue` is the value-level quantity; the paper-faithful
signed q and the genuine comparison are explicitly not proved
(`SourceQSideComparison` header, gap note).

### G5. Final contract construction
`Contract.lean` says the ordered conclusion is proved from `StepXIContract`,
but construction of the contract from IUT source data is unfinished; no
placeholder theorem is exported.

### G6. One-factor/local A simplification in tmp work
The tmp `qVFamTensorV = Unit` and L/rootTensorBlock branches are NOT repo
objects.  Repo's Cor312 uses value monoids, not a one-factor p-adic tensor.
Do not mix them.

## 3. What is actually aligned and usable

- `OriginalInput` source fields (actual).
- `ThetaPilotCarrier`, `ThetaPilotPoint`, `sourceThetaPilotPoint`.
- `possibleThetaPilotImageSet`, `sourceHolomorphicHull`, `holomorphicHull` universal properties.
- `sourceQSideNormalizedValue`, `sourceSetVolume` value-level identities.
- `StepXIContract`/`CertificateHullWiring` conditional final assembly.
- `TwoLthRootQVActual` conditional root API and exact gap.

## 4. Construction order from gaps

1. Decide the literal paper carrier: extend `OriginalInput` with the actual IQ
   carrier/log-shell/Haar (G1), or prove that the value-monoid model suffices
   for the final log-volume comparison (not currently proved).
2. Construct actual `q_v^(j^2)` packet/root in the chosen carrier (G2).
3. Construct Ind1/2/3 actions and the image union on that carrier (G3).
4. Construct the signed q-side carrier and the genuine comparison (G4).
5. Build `StepXIContract`/`IQHullLogVolumeInterface` from the actual source (G5).

Do not build more tmp p-adic surrogates before G1 is decided.
