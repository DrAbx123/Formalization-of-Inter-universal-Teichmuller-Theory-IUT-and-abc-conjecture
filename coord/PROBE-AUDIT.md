# PROBE-AUDIT — 2026-11-11 (shehdd A465 probe cleanup audit)

**Trigger**: during A465 probe-infra maintenance the incremental script additionally deleted 1849 probe files whose source latest result was non-EXIT0 or missing (most had never been compiled / had no results record).

**New rule (effective now)**: probe generator is APPEND-ONLY - only create probes for latest-EXIT0 sources without a probe; NO DELETION of probe files. extra-targets only dedupe/sort/append. This audit + the 16 rebuilds are a one-off recovery.

## Deleted probes that have results records: 36 (30 last-EXIT0 + 6 last-EXIT1)

16 AutoProbe files rebuilt under their original names (source file + first 3 declarations #print axioms); 20 legacy hand-written probes NOT rebuilt.

### Rebuilt (16)

| probe | last EXIT | rebuilt from |
|---|---|---|
| _AutoProbe_Mzk1StepVPaperActual | 0 | Mzk1StepVPaperActual.lean rebuilt |
| _AutoProbe_Mzk1Cor312TargetWiringActual | 0 | Mzk1Cor312TargetWiringActual.lean rebuilt |
| _AutoProbe_Mzk1IUTIIILinkActual | 0 | Mzk1IUTIIILinkActual.lean rebuilt |
| _AutoProbe_Mzk1KummerThetaInterfaceActual | 0 | Mzk1KummerThetaInterfaceActual.lean rebuilt |
| _AutoProbe_Mzk1G2CDConsumerActual | 0 | Mzk1G2CDConsumerActual.lean rebuilt |
| _AutoProbe_Mzk1R9PointMembershipConsumerActual | 0 | Mzk1R9PointMembershipConsumerActual.lean rebuilt |
| _AutoProbe_Mzk1GeomCoreFiniteMapChartInterfaceActual | 0 | Mzk1GeomCoreFiniteMapChartInterfaceActual.lean rebuilt |
| _AutoProbe_Mzk1GeomCoreLineBundleInterfaceActual | 0 | Mzk1GeomCoreLineBundleInterfaceActual.lean rebuilt |
| _AutoProbe_Mzk1Thm110SlackActual | 0 | Mzk1Thm110SlackActual.lean rebuilt |
| _AutoProbe_Mzk1E5UniformHeightActual | 0 | Mzk1E5UniformHeightActual.lean rebuilt |
| _AutoProbe_Mzk1Prop58iConcreteActual | 0 | Mzk1Prop58iConcreteActual.lean rebuilt |
| _AutoProbe_Mzk1StepXIContractConstructionActual | 0 | Mzk1StepXIContractConstructionActual.lean rebuilt |
| _AutoProbe_Mzk1Cor312ObligationConsumerActual | 0 | Mzk1Cor312ObligationConsumerActual.lean rebuilt |
| _AutoProbe_Mzk1R9HullConsumerActual | 0 | Mzk1R9HullConsumerActual.lean rebuilt |
| _AutoProbe_Hull13TwoSidedBoundActual | 0 | Hull13TwoSidedBoundActual.lean rebuilt |
| _AutoProbe_AbsTopIII05Section0ObjectsActual | 0 | AbsTopIII05Section0ObjectsActual.lean rebuilt |

### Not rebuilt: legacy hand-written probes (20) and reasons

| probe | last EXIT | source candidate | reason |
|---|---|---|---|
| _S3127AffineCoverProbe | 1 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S2550Probe1 | 1 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814ProbeAPI | 1 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814ProbeState | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe6 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe0 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe1 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe7 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe2 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe3 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S2433Probe2 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe5 | 1 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S1814Probe4 | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S3127G2BaseSpecProbe | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _S3136Stage4HostProbe | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _HaarBodyProbeActual | 0 | n/a | old probe name cannot be mapped uniquely to a current source (S1814/S2433/S3127/S3136/HaarBody legacy families) |
| _Mzk1StepProviderPrimeProbe | 0 | Mzk1StepProviderPrimeActual | source currently EXIT1 (actively owned lane) |
| _Mzk1GeomCoreLineBundleBridgeProbeActual | 0 | Mzk1GeomCoreLineBundleBridgeActual | source candidate non-EXIT0 or absent |
| _ProbeMzk1EtThGapStatementActual | 1 | Mzk1EtThGapStatementActual | source candidate non-EXIT0 or absent |
| _Mzk1GeomCoreChartBridgeLineBundleConsumerProbeActual | 1 | Mzk1GeomCoreChartBridgeLineBundleConsumerActual | source candidate non-EXIT0 or absent |

## Reference check (fragments / notes / pins)

- coord/paper-chain/target-chain.route-mentions.json has two DEF route-mention nodes citing _S3136Stage4HostProbe (historical AUDIT_LEDGER line / priority list); these are NOT CITABLE pins and were left untouched.
- Main coord/dag fragments, route index and CITABLE pin notes contain NO references to any other deleted probe name (all hits are watchdog generated caches: graph-cache/order/extra-targets).
- Conclusion: NO CITABLE pin affected. If a hand-recorded pin referenced one of these probes, provide the file path and the probe can be rebuilt from the node declarations.

## Current probe infra state

- tmp/sheaf/xif/paper/_AutoProbe_*.lean: 325 files
- dag/watchdog/extra-targets.txt: 851 entries after append-only refresh (non-probe + auto probes; dead entries for absent files removed)
- tools/_shehdd_auto_probes.mjs: append-only (no unlink).

## Appendix: route-index rows referencing cleaned probes

Route index rows _FinalPaperXiFProbe, _PaperTargetProbe, _S1779RouteProbe, _s2857gaprobe were probe-only rows (decls=[]), i.e. never CITABLE pins; they are now annotated STALE_NO_SOURCE with index_note pointing here instead of being rebuilt (rebuild available on demand from node declarations). 	tmp/TauCetiPort/TauCeti/LinearAlgebra/Matrix/Alternating.lean is a pre-existing stale index row (missing path), unrelated to probe cleanup.

## Verification of rebuilt probes

- Rebuilt 16 AutoProbes: EXIT0=16, pending=0, EXIT1=0.
- _AutoProbe_Mzk1StepVPaperActual: EXIT0
- _AutoProbe_Mzk1Cor312TargetWiringActual: EXIT0
- _AutoProbe_Mzk1IUTIIILinkActual: EXIT0
- _AutoProbe_Mzk1KummerThetaInterfaceActual: EXIT0
- _AutoProbe_Mzk1G2CDConsumerActual: EXIT0
- _AutoProbe_Mzk1R9PointMembershipConsumerActual: EXIT0
- _AutoProbe_Mzk1GeomCoreFiniteMapChartInterfaceActual: EXIT0
- _AutoProbe_Mzk1GeomCoreLineBundleInterfaceActual: EXIT0
- _AutoProbe_Mzk1Thm110SlackActual: EXIT0
- _AutoProbe_Mzk1E5UniformHeightActual: EXIT0
- _AutoProbe_Mzk1Prop58iConcreteActual: EXIT0
- _AutoProbe_Mzk1StepXIContractConstructionActual: EXIT0
- _AutoProbe_Mzk1Cor312ObligationConsumerActual: EXIT0
- _AutoProbe_Mzk1R9HullConsumerActual: EXIT0
- _AutoProbe_Hull13TwoSidedBoundActual: EXIT0
- _AutoProbe_AbsTopIII05Section0ObjectsActual: EXIT0

## Status note (2026-11-10T17:48:10.333Z-ish)

- AutoProbe files: 315.
- 130 EXIT0 / 8 stale-record EXIT1 (contents verified correct after multi-namespace FQN fix; awaiting watchdog recompile).

## Appendix: generator hardening (2026-11-10T17:55:57.577Z)

- Multi-namespace FQN: scope-stack parser (namespace vs section separated).
- Comment stripping: block comments and line comments are removed before declaration scan, so docstring pseudo-declarations (for example a doc line starting with the word theorem) no longer produce invalid #print axioms targets.
- Declaration regex now accepts names ending at end-of-line.
- 315 AutoProbe files; 37 probes content-updated by comment-stripping pass; no deletions.

## Priority-file probes (2026-11-10T18:19:09.993Z)

- Generated probe files for green priority files lacking probes: Mzk1AbsoluteKummerTrioSummaryActual, Mzk1FrobeniusGraphAutClosureActual, Mzk1GraphAutTranslationUnicityActual, Mzk1FrobeniusPictureArrowFactsActual, Mzk1ABCBridgeNonemptyIffActual, Mzk1V2UnfoldActual, Mzk1T3GapPackageActual, Mzk1Section0SaturationLawsActual, Mzk1Section0FinLinearLawsActual, Mzk1Section0GraphAutActual, Mzk1H5HullClosureLawsActual, Mzk1H5HullRayLawsActual, Mzk1H7Ob9SandwichLawsActual, Mzk1EtThKernelLatticeLawsActual.
- AutoProbe total: 325.
