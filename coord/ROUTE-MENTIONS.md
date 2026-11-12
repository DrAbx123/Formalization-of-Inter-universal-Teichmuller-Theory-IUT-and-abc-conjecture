# ROUTE MENTIONS — route/Stage/3.11.5/SHE/APT/IPL/alternative/failure/obstruction mentions in coord docs (Lead A440)

**Scope:** mined coord/*.md (140 files, 2,949,923B) + key route docs; raw grep saved `tmp/route_mentions_raw.csv` (4119 matches). This file curates: 出处 -> 路线摘要 -> 状态 -> 是否已入 DAG. Research map only; NO proofs; NO gate edit. Gate anchor V150@18248/CFC6CE08; GATE NOT PASSED; binding HOLD; L8 FROZEN.

## A. NAMED ALTERNATIVE / ROUTE FAMILIES

| # | route | 出处 (file:line) | 摘要 | 状态 | 已入 DAG? |
|---|---|---|---|---|---|
| R1 | Direct-readout / fixed-shell route | `IUT-ROUTE-ETA-V2.md`:8,10,12,34; `IUT-ROUTE-ETA.md`:62 | fixed-shell discrepancy = ±q readout; singleton/fixed-shell Rss (Subsingleton by proof irrelevance); abstract `Nonempty VerticalLogKummerCorrespondence` with no X/site/shell content; direct closures invalidated/archived | **ARCHIVED / negative control (DEAD)** | **NO** (no route ids; fixed-shell tokens absent) |
| R2 | Eta-algorithm alternative (LANA) | `IUT-ROUTE-ETA.md`:23-62,84-85; `IUT-ROUTE-ETA-V2.md`:18,30,45,54 | `eta^anab_S : R^val -> R^ss` from anabelian/Kummer/log-shell reconstruction + chosen integral structure S; EtaValueGroupLineActual (nontrivial Rval/pilot, zero sorry); EtaIntegralStructureS (Ind1/2/3 laws, zero sorry); EtaRssNontrivialActual (varying-region quotient, two classes) | **ACTIVE / EXPERIMENTAL** (target_accepted=false; MissingQCalibrationBridge gap) | **NO** (eta route ids absent; theta ids are different) |
| R3 | Paper Stages 1-5 / four triangles | `IUT-PAPER-ROUTE.md`:8,27-42; `IUT-STAGE-AUDIT-20261109.md`:11-30 | Stage 1: Thm 3.11 => Cor 3.12, four triangles (BPS->multiradial, dsc, HDD=hull+det∘dsc, 4th (HDD)∘SHE=q vs Theta); Stage 2: Thm3.11 modulo IUTchI-II; Stage 3: IUTchI-II modulo 1995-2015; Stage 4 earlier results; Stage 5 numeric/effective; 3.11.5=>3.12 = fourth triangle | **AUDIT MAP / DESIGN** (BPS ABSENT named; Stage-1 dsc missing; APT only evidence/transport; HDD framework) | **PARTIAL** (paper nodes `iutiii:PAPER.S3180.ABC_CONDITIONAL`, `iutiii:PAPER.S3182.COR312_HULLDET`; no Stage/BPS/dsc/HDD/APT ids) |
| R4 | N8 closure route (dsc+APT+IPL) | `N8-CLOSURE-ROUTE.md`:3,14,29,38,66,86,106,115,129,223,240 | BPS -> multiradial representation up to (Ind1,2,3); (dsc) descent arrow; (HDD):=(hull+det)∘(dsc); (HDD)∘(SHE)=q-pilot vs Theta-pilot comparison = Cor 3.12; Thm3.11=dsc+APT+IPL; 3.11.5=>3.12=HDD∘dsc+SHE+IPL; no free ipl/she/apt/q_le_hull | **DESIGN / PLANNED** (tmp/sheaf/n8/closure proposals; C5 SourceAlgorithmCompatibility design) | **NO** |
| R5 | Endgame Option-B model route | `ENDGAME-DEPENDENCY-LEDGER.md`:37-42,60-62 | third-reopen notes: (i) qpilot-adapted model V=S3135ModelV (if theater pullback greens) or (ii) CHEAP fallback V=sourceHaarActualOriginalInput (V=Unit, q=1); F4 by construction + minus-1 witness; model-route Option B finalized (not applied) | **PREPARED / AWAIT GO** (not applied; awaits audit+GO) | **PARTIAL** (cor312 bridge nodes; no S3135ModelV id) |
| R6 | Fourth-triangle label 3.11.5 | `IUT-PAPER-ROUTE.md`:30-31; `ENDGAME-DEPENDENCY-LEDGER.md`:60-61 | "3.11.5 => 3.12" = (hull+det)∘(dsc)+SHE+IPL; report label; string "3.11.5 (=3.11+Rmk 3.9.5)" never appears in papers | **CONCEPT/LABEL only** | **NO** (3.11.5 token 0 in DAG) |
| R7 | abc concrete paper-lambda route | `FINAL-STATUS-20261110.md`:71; `MAINLINE_ABC_F.md` (route sections) | S3135PaperLambdaConcreteActual: concrete normalized model sets scaling:=1 (SourceUnitRegionHaarDataActual:421), Example 3.6 shell | **PARTIAL concrete** | **PARTIAL** (endgame/cor312 nodes; no paper-lambda id) |
| R8 | Historical log-shell-carrier / api5 one-column | `HISTORY_ARCHAEOLOGY.md`:73,84 | log-shell-carrier-20261016: 0 probes/9; api5-one-column-landing: APT transport actual/conditional, no source q-pilot | **HISTORICAL (probes only) / DEAD for route** | **NO** |
| R9 | Weighted / global q-pilot route | `HISTORY_ARCHAEOLOGY.md`:148-150 | weighted q-pilot formula actual; global q-pilot equals unweighted sourceQPilotSignedLog (not paper weighted); S2807 theta-hull identity only; SG3 upper gap remains | **PARTIAL / HISTORICAL** | **PARTIAL** (theta nodes; no weighted-q id) |
| R10 | Pointwise Q.IsStack / prestack obstruction | `HISTORY_ARCHAEOLOGY.md`:338,364 | S1971/S2870 prestack obstruction; gap-exploration report 20261030 | **OBSTRUCTION** | **NO** |

## B. FOURTH-TRIANGLE / SHE / APT / IPL MENTIONS (aggregate)

- `ENDGAME-DEPENDENCY-LEDGER.md`:60-61: (dsc)+APT+IPL => Thm3.11; (hull+det)∘(dsc)+SHE+IPL => Cor3.12.
- `N8-CLOSURE-ROUTE.md`:14,29,86,115,129,223: IPL/SHE/APT compatibility C5; no free ipl/she/apt/q_le_hull/degree_preserved/possibleImage; SourceAlgorithmCompatibility group5.
- `IUT-STAGE-AUDIT-20261109.md`:25-30: BPS ABSENT named; dsc missing as Stage-1 arrow; HDD framework files; APT only evidence/transport.
- `IUT-PAPER-ROUTE.md`:30-31: descent (dsc)/APT/IPL/SHE; 3.11.5=>3.12 fourth triangle.
- **DAG status:** tokens `APT`, `IPL`, `3.11.5`, `Stage`, `BPS`, `dsc`, `HDD`, `obstruction` => **0 node ids**; SHE-related DAG ids are only LogShell tree nodes (5: ThetaLogShell, LogShellCarrier, LogShellAbsTopIII, LogShellHull, LOGSHELL_MUN), not the SHE operation.

## C. FAILURE / OBSTRUCTION / COUNTEREXAMPLE / DEAD-END MENTIONS

| # | obstruction | 出处 | 摘要 | 状态 | 已入 DAG? |
|---|---|---|---|---|---|
| O1 | SG3b tensor Haar product | `E-EXISTING-CLOSURE-MAP.md`:35; SG3B blocker note; `FOUNDATION-FIRST-PLAN.md` E-2 | `actualC3LogShellTensorLogVolume C3 = packetLogVolume packet` has NO actual product-Haar formula; set-level image only; no fake packet | **OBSTRUCTION (named)** | **NO** (SG3 token 0) |
| O2 | S2826 C3 region fractional | `S2826_C3_REGION_FRACTIONAL.md`; `FOUNDATION-FIRST-PLAN.md` E-2 | C3 region vs fractional-lattice region formula NOT actual; S349C3TensorLatticeRegionActual lattice region only | **OBSTRUCTION** | **NO** (S2826 token 0) |
| O3 | S2804 Cor312 <=> UpperGap | `S2804_COR312_INVENTORY.md`; E plan E-5 | Cor312 reduces to S2717UpperGap; not a self-contained proof | **REDUCTION / TARGET GAP** | **NO** (S2804 token 0; cor312 bridge nodes exist) |
| O4 | modelIndex_not_subsingleton lattice obstruction | `ENDGAME-DEPENDENCY-LEDGER.md`:25 | index-dependent theater family distinctness+alignment obstruction documented | **OBSTRUCTION** | **PARTIAL** (endgame nodes; no obstruction id) |
| O5 | NativeC3 genuine sorry | `FINAL-STATUS-20261110.md`:61 | only genuine `sorry` in mainline import closure scan (NativeC3 donor nonemptiness); NOT a closure | **KNOWN GAP (never cite as proof)** | **PARTIAL** |
| O6 | direct-readout frozen/relaxed routes invalidated | `IUT-ROUTE-ETA.md`:62; `IUT-ROUTE-ETA-V2.md`:34 | frozen/relaxed direct-readout paper closures invalidated, not counted; archived negative controls | **DEAD** | **NO** |
| O7 | fixed-shell singleton degeneracy | `IUT-ROUTE-ETA-V2.md`:8-10 | fixed-shell Rss Subsingleton by proof irrelevance; must use varying admissible regions | **DEAD / NEGATIVE CONTROL** | **NO** |

## D. DAG INCLUSION SUMMARY (A440)

- DAG merge A439: 154 nodes / 159 edges / 0 conflicts (sources main 26/21; iuti-ii 31/37; iutiii 29/23; iutiv-abc 36/52; theta-etth 32/26).
- Route/process tokens absent from DAG ids: APT 0; IPL 0; 3.11.5 0; Stage 0; BPS 0; dsc 0; HDD 0; obstruction 0; S2804/S2826/SG3 0.
- Route-ish DAG ids present: `iutiv-abc:G3.route.gapReduced` / `...gapReducedV2` / `...pointwiseReduced` / `...pointwiseWeakened`; paper nodes `iutiii:PAPER.S3180.ABC_CONDITIONAL`, `iutiii:PAPER.S3182.COR312_HULLDET`; cor312 nodes T1-cor312-abc-bridge, T6-iut4-theta-two-sided.
- `coord/target-chain.paper-routes.json` (hull; prefix paper:; Stage1-5 + §4 species/mutation) **EXPECTED but NOT YET delivered**; paper nodes statuses allowed GAP/NAMED; merge last per A439.
- Graph rebuild (mainline A438): import cycle S3139 fixed (direct imports replace umbrella; CopyAction EXIT0 7247B); dag/generated 123410/36617; validator ok=true, cyclic 0.

## E. NOTES

- Mining method: PowerShell Select-String over coord/*.md + key route docs; raw matches `tmp/route_mentions_raw.csv` (4119 rows, 140 files, 2.95MB); curated here by route family (not exhaustive line dump).
- No proofs; no gate edit; statuses quoted from sources; DAG token checks against `dag/declaration-dag.json`.
- Prepared by lattice under Lead A440; update when paper-routes fragment lands or routes change.

