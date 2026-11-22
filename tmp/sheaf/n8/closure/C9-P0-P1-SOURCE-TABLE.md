# C9 P0/P1 source-object table (stage 1)

Date 2026-10-23. No Lean changes. Source route: IUT III Th.3.11, Remark 3.10.2,
Remark 3.11.1, Cor.3.12; supplement C9-STAGE1-SUPPLEMENT-ROUTE-20261023.

Legend: status = actual / partial / missing / statement-gap.  This is a source inventory,
not a proof and not an accepted Lean target.

## P0: input/index objects

| object | role | indices | existing declaration | status |
|---|---|---|---|---|
| `S : SourceNativeInitialThetaData l` | qualified Definition 3.1 input | `l` | `InitialThetaSource.SourceNativeInitialThetaData` | partial (semantic review of full native contract pending) |
| `V` section | selected places over Fmod | `v in V(S)` | `S.tuple.source.V`; `V_mod_bijection`; `V_place_comap` | actual data, C1 place slice partial |
| arithmetic tower | `F`, `Fmod`, `K`, `Fbar` | — | `S.arithmetic` | actual fields |
| local places | finite/infinite place at K/Fmod | `v`, `p` | `NumberFieldPlace`, `FinitePlaceAtPrime` | actual carriers |
| lattice `L` | actual theater/log-theta-lattice | `(n,m)` columns/rows | no full Lean type; `NativeLattice` has family + arithmetic alignment | statement gap |
| Hodge theater | theta packet, prime strip | `(n,m)`, `j`, `v` | `HodgeTheater`; `SourceHodgeTheaterFamily` | partial legacy abstraction; not identified with paper L |
| theta packet | finite theta special values | `(n,m)`, `j` | `FiniteThetaPacket` | actual scale/q data, not source q identity |
| prime strip | local monoid/Pi/action | place `v` | `FPrimeStrip`, `.Mon`, `.Pi`, `.action` | actual production type |
| log-shell/local log | local units/log | `p`, place | `SourceLogShellDatum`, `sourceLocalLogShellDatum` | actual finite-place slice |
| q candidate | actual completion q | finite place | `FinitePlaceQCandidate`; `NativeC3.nativeQActual` from Clause (b) | actual native q; source curve identification residual |
| tensor index/tuple | ArithmeticTensorTupleBlock factors | `i`, tuple | `NativeC3.NativeTensorLandingDonor` (missing) | missing actual landing to tensor block |
| processions | `n in Z` (and columns m) | `n,m` | `ThetaPilotCarrier` finite index only | `ThetaPilotCarrier` is not all `(n,m)`; statement gap |

## P1: complete source output/representation objects

| object | paper role | indices | existing declaration | status |
|---|---|---|---|---|
| complete allowed choice `alpha` | one full source-allowed choice (places/tensor packet/procession/Ind) | `alpha` | none; current C4 `Choice` is `SignedLabel` only | missing; `j` is not `alpha` |
| `R_alpha` | output region family in target structure | `alpha`, local places/tuple | none; current `C4.U` is finite set of eval points | missing actual region construction |
| `RawPoss` | original source output family | `alpha` | candidate: `C4.Witness`/`eval`/`U` | partial candidate, not complete pilot/ind |
| `U` | union of RawPoss | input config | `C4.U` | partial; finite point image, no admissible region |
| `H` | paper holomorphic hull of U | config | `I.sourceHolomorphicHull` (value carrier); C7 canonical IQ hull | source hull actual but wrong/free scaling; no paper IQ H |
| `HullPoss` | Stp4 enlarged allowed regions | config | none | missing |
| Ind1/Ind2/Ind3 | allowed indeterminacies | `n`, labels | `IndActionData` uses provisional `[Group Label]` | partial/wrong label object (LabelData pending) |
| Kummer/Galois evaluation | reconstruct Theta-pilot representation | `(n,m)`, j | `SourceKummerEvaluationSquareExtension` conditional; T11 interface | partial; actual arrows/unit portion missing |
| theta image | value/tensor output | `n,j` | `SourceThetaIQInterface.thetaImage` | interface field, no source identification |
| q-pilot representation `Rq` | independent q output | q configuration | `C9QPilotRegion.qPilotRegionSource` singleton completion q; `QPaperScalar` | scalar/point actual; region/global L missing |
| global log-volume `L` | same global signed procession-normalized volume on Adm | region | `SourceOModuleCompactness_haarData` local; `C6ActualIQData.normalizedLogVolume` single block | global weights/procession/Adm missing |
| `Values` | `{L(R) | R in HullPoss}` | config | `C9Paper.ValuesPaper` arbitrary provenance/subsets; `C9ValuesPaper.outputRegion` finite point image | not admissible; rejected |
| `Theta` | `L(H)` with Theta finite | config | no accepted declaration | missing |

## P0/P1 conclusion

- P0 has native S, place data, local log-shell, finite theta packet, actual q; full lattice L and all `(n,m)` indices are statement gaps.
- P1 has only partial RawPoss via C4 eval/U; complete alpha, R_alpha, HullPoss, global L, Theta are missing.
- Current QPaper singleton/finite-point ValuesPaper/free thetaToC6 are not accepted P1 objects.
- Next: resolve the complete alpha/R_alpha representation and the lattice type before Lean implementation.
