# Alternative route after IUT critiques: eta-algorithm / log-shell path

Date 2026-10-24. User instruction: read critique articles, avoid paths they refute, look at other paths.

## Criticized paths to avoid

Scholze-Stix (Why abc is still a conjecture):
- direct comparison of abstract/concrete pilots across the Theta-link;
- trivializing all real lines to a common R and then demanding commutativity;
- identifying copies of R without preserving construction/scaling;
- O(l^2)/monodromy factors make the direct comparison powerless.

LANA report:
- confirms the Scholze-Stix hexagon does not commute;
- confirms that if Cor.3.12 were derived through that diagram, a factor O(l^2) would be needed.

Consequences for this project:
- do NOT use direct Q-scalar vs hull-volume comparison as the source theorem;
- do NOT use a constant/underconstrained global L donor;
- do NOT count a degenerate readout (reference=region, Theta=0) as paper N8;
- frozen/relaxed direct-readout routes are archived as negative controls only.

## Alternative path (LANA eta-algorithm)

Compare two constructions BEFORE degrees:

eta^q : R^val -> R^ss   from the q-pilot/native arithmetic holomorphic structure;
eta^anab_S : R^val -> R^ss   from the anabelian/Kummer/log-shell reconstruction and a chosen integral structure S.

Goal:

exists suitable S, eta^q = eta^anab_S.

Only after this comparison pass to the common volume container and compare normalized log-volumes.
The final inequality is on the SAME side of the Theta-link.

## Lean mapping

- `Rval`: actual value-group real line with pilot from native q/selected places;
- `Rss`: real line from log-shells/volume containers (production log-shell API);
- `EtaQ`: actual construction from native q/Tate data;
- `EtaAnab S`: actual anabelian/Kummer/log-shell construction;
- `EtaComparison`: exact proposition `etaQ = etaAnab S`; named source gap until proved;
- `EtaConclusion`: derive Q<=Theta / normalized inequality only from Etacomparison, never directly from a scalar sign.

## Hard constraints

1. preserve unit/value groups and log-shell integral structure;
2. no trivialized common R;
3. Ind1/2/3 encoded through admissible S/construction, not free Real adjustments;
4. no direct Q/hull comparison;
5. exact named gaps for eta equality if unproved;
6. if eta equality is false/undecidable from production, report exact no-go.

## Reuse

- production log-shell modules (`LogShellVolume*`, `integralLogShell`, Kummer vertical log layers);
- native q/Tate data; C1/C3 actual slices; C6/C7 hull data only as donors after eta comparison.

## Status

Active alternative route. Frozen/relaxed direct-readout paper closures invalidated, not counted. target_accepted=false.

## Critique→route audit (2026-10-24)

Audit file: IUT-CRITIQUE-ROUTE-AUDIT.md, SHA 5E6DBBBF4E6252FB84EC4E9280CE4231E066D217A2781C2735005057EA756EF2.

FORBIDDEN: direct Q<=Theta/qPilot=hull scalar comparison; collapsing Rval=Rss=Real; degree comparison before eta; degenerate reference=region/Theta=0/Values={0}/JRange=univ; free Real Ind adjustments; imported theorem/arbitrary donor.

SUPPORTED donors: IntegralLogShell/LogShellVolume/SourceLogShell, Example36 log-shell lattice/Frobenius, native q/Tate + SourceImageHull, C1/C3 actual slices, nonarch/arch Adm after reference!=region.

EXACT GAPS: actual Rval, Rss, EtaQ, EtaAnab S, EtaComparison, post-eta common volume, nonzero Theta/Values, actual Q<=Theta.

Next packages: ETA-8a Rval, ETA-8b Rss, ETA-8c EtaQ, ETA-8d EtaAnab, ETA-8e EtaComparison, ETA-8f post-eta volume/Q<=Theta with guards.

## ETA-5 actual Rval (2026-10-24)

- EtaValueGroupLineActual.lean SHA 1E0FE7A9F49F132337531B05ACBBDA7046C5941ADB26249F1C5B63277AD25E57, exit0 zero sorry.
- Rval := Multiplicative Real (not trivialized common R); pilot from qPilotKummerRelativeVolume, pilot != 1; selected places nonempty.
- No Q/hull comparison, no free pilot/Real.

## ETA actual progress (2026-10-24)

- EtaValueGroupLineActual: actual Rval/pilot (Multiplicative Real nontrivial), zero sorry.
- EtaIntegralStructureS: actual integralLogShell/logShellVolume/finiteOutput S with Ind1/2/3 laws, zero sorry.
- EtaQActual: actual qUnit/qScalar + exact missing Rval->Rss q-map (named).
- EtaComparisonReduction: exact full->pilot comparison reduction; Rss:=Real risk flagged, corrected Rss log-shell line dispatched.
- EtaRouteInterface: EtaQ/EtaAnab defined as inverse scalings from logShell=invScaledPreLogShell; may be tautological (semantic audit requested). Do not count as LANA eta equality until audit.
- No direct Q/hull comparison counted; target_accepted=false.

## EtaRouteInterface negative control (2026-10-24)

- EtaRouteInterfaceSemanticAudit: EtaQ/EtaAnab are inverse p* scalings from logShell=invScaledPreLogShell; EtaComparison is inverse laws + q<0. NOT independent LANA constructions. Mark negative control; do not count.
- Actual pieces retained: EtaValueGroupLineActual (Rval/pilot), EtaIntegralStructureS (integralLogShell/logShellVolume/Ind), EtaRssLogShellLine (log-shell Rss, zero sorry), EtaRvalCoherence.
- Exact independent gaps: q-side eta^q map (logMap/qPilot connection); native G_v/Kummer/archimedean log-shell action; nontrivial eta comparison.

## ETA residue target correction (2026-10-24)

- EtaResidueMatchAttempt: Clause B forces l coprime to residueCharacteristic(badBasePlace); equality is FALSE.
- Therefore ETA-6 S fixed at Q_[l.value] is incompatible with the selected native bad place; EtaIntegralStructureSourceBridge residue gap cannot be fulfilled.
- Corrected target: integral structure/readout at actual selected bad native place (generic localField/Completion), not fixed Q_l. EtaIntegralStructureAtSelectedPlace task active.
- S/Ind actual results retained only as abstract log-shell construction, not source-bound until re-based at selected place.

## ETA selected-place correction actual (2026-10-24)

- EtaResidueMatchAttempt: l coprime/unequal to selected bad residue; Q_l-based S impossible.
- EtaIntegralStructureAtSelectedPlace: zero-sorry actual S at SelectedCompletion of actual selected bad native place; production integralLogShell/logShellVolume/finiteOutput/Ind laws; no residue equality asserted.
- EtaRssComparisonReduction: Rss=log-shell Rss (EtaRssLogShellLineData), not Real; one named maps gap.
- EtaKummerLogLink: actual Kummer/log-shell facts, one source-datum gap.
- Remaining independent etaQ/etaAnab maps and nontrivial comparison; ETA route open.

## EtaComparisonNontrivial audit (2026-10-24)

- Audit: EtaComparisonNontrivial uses scalarized Multiplicative Real codomain, not actual Rss=logShell; etaAnab is a named interface, value_eq is only pilot fixed point. Archive as non-eta-route; reuse only etaQMapInterface and qUnit value.
- Corrected task: EtaSquareIdentitiesActual with actual Rval=preLogShell/Rss=logShell and scalar observations; no common Real line.

## ETA selected-place actual bridge (2026-10-24)

- EtaIntegralStructureAtSelectedPlace: actual S at selected bad completion, zero sorry.
- EtaSelectedPlaceReadout: actual selected shell/volumeIndex/logVolume/q; exact EtaSelectedPlaceQPilotGap.
- EtaRssSelectedPlaceBridge: actual Rss volumeIndex = selected volumeIndex, zero sorry; no old Q_l S/common Real.
- Remaining q-side: actual q carrier -> selected shell map (carrier audit/attempt active); etaAnab source datum; nontrivial square comparison.

## Eta q vs volume-index raw equality false (2026-10-24)

- EtaSelectedPlaceQPilotGap (log volumeIndex = nativeQParameter) is structurally FALSE: volumeIndex positive Nat -> log>=0; qParameter=exp(-n) in (0,1).
- Target correction: need an explicitly normalized log-volume comparison, not raw q=log index. EtaNormalizedComparisonTarget task active.
- Do not use raw equality or scalar sign as eta comparison.

## ETA F-place actual + nondegeneracy core (2026-10-24)

- EtaFPlaceNormalizedComparison: actual F-place shell/readout, normalized q volume; exact normalized gap.
- EtaNondegeneracyActual: actual Rval nontrivial/pilot ne_one/Rss nonempty/integral nonempty; exact remaining guards properness/theta/values/ref-region/nonconstant.
- Raw q=log volume no-go; Q_l residue no-go; scaling/scalarized comparisons archived.
- Remaining: F-place normalized equality, qToFShell map, etaAnab source datum, nontrivial comparison.

## ETA qToFShell actual map (2026-10-24)

- EtaQToFShellActual: actual F-shell units map using C1P6QUniformizerNormalization.unit transported via normalizedCompletionIntegersEquiv; logMap value. No Fmod ring equiv/arbitrary map.
- Remaining exact gaps: qToShellValue ∈ fPlaceShell.logShell; qToShellValue ≠ 0.
- F-place shell/volume consumer from EtaFPlaceNormalizedComparison used; raw native q valuation <1 is not an integral shell unit.

## ETA Kummer source datum actual + carrier conflict (2026-10-24)

- EtaKummerSourceDatumActual/EtaKummerLogLink: actual SourceLogShellDatum from C2Native.nativeLocalShell (Fmod), zero sorry; codomainKummerContained actual via invariants=top.
- Carrier audit: etaAnab/q now at F-place; Fmod shell source datum is wrong level. Corrected F-level source datum task dispatched; no Fmod/F mixing allowed.

## ETA properness actual (2026-10-24)

- EtaIntegralProperActual zero sorry: integralLogShell != univ via compactness vs noncompact Q_l; etaIntegral_proper_actual derived.
- EtaNondegeneracyActual updated: properness proved; only EtaRemainingGuards (Theta!=0/Values!={0}/reference!=region/nonconstant) named.

## ETA latest exact state (2026-10-24)

- EtaQToFShellValueActual: QToShellValueMem conditional on production fPlaceShell.codomainKummerContained; QToShellValueNeZero equivalent to normalization unit non-torsion. Both exact gaps.
- EtaSignedCriterionDisproof: signed target reduced to exact production equation fPlaceVolumeIndex = residueNormBase^order; global truth/falsity not settled; volumeIndex=1 is false branch.
- EtaSquareIdentitiesActual: actual nonzero scalar square identities; only global zero extension MissingGlobalScalarSquare.
- EtaConsumerIndependent: independent eta comparison consumer with named etaComparisonIndependent/etaQNormalizedIdentification; pStar tautology not used.
- No target accepted; ETA route remains exact named gaps.

## ETA volume-index formula (2026-10-24)

- EtaVolumeIndexFormulaAttempt: conditional actual QFE formula fPlaceVolumeIndex = residueCard^(e*s-1)*(residueCard-1)/#torsion; signed criterion iff exact integer gap vs residueNormBase^order.
- Missing: LogShellQFECardinalityHypothesis at F-place and native q.order vs e/f relation. No arbitrary normalization/equality.

## ETA guards actual (2026-10-24)

- EtaGuardsActualAttempt: Theta!=0/Values!={0}/reference!=region actual from nondegenerate finite readout; comparison nonconstant exact named gap. Caveat: F-place slice only, not global P6 Theta/Values.
- EtaFPlace Kummer vertical/consumer/guards integration tasks active.
