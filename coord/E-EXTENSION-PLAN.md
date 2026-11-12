# E-EXTENSION PLAN (skeleton; Lead A426) — per-Problem-E item: existing closures -> missing layer -> paper-faithful extension steps -> reusable assets

**Status:** notes only; NO proofs written here; NO gate edit. Canonical gate unchanged: V150@18248/CFC6CE08; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800; no un-HOLD; no queue binding; no registry edits.

**Sources:** coord/PROBLEM-E-INVENTORY.md (mainline 7119B); coord/FOUNDATIONS-IUTIV.md (16984B stepxi inventory); FOUNDATION-FIRST-PLAN.md; paper lines cited per item.

**Merge status (A427):** E mapping skeleton ready here; mainline `E-EXISTING-CLOSURE-MAP.md` not yet delivered; merge checklist below. **Merge prep:** `coord/E-EXISTING-CLOSURE-MAP.md` is mainline-authored (hull/qpilot/stepxi/abc contributions) and NOT YET delivered. Merge checklist: (1) reconcile every closure pin with this plan tables; (2) add paper line refs per item; (3) mark named/class-B vs proved consistently; (4) no proof claims, no gate rows; (5) after merge, keep this file as the E-extension source of truth.

## E-1 AbsTopIII05 (deep named construction)

- **Existing closures:** `AbsTopIII05RefinedActual` 10562B sha 08816FDE CITABLE 16 probe_ok (D1 Prop58iLocalFieldReconstruction / D2 Prop58iiLogShellReconstruction / D3 Cor55 bridge anchor / D4 Z-graph action anchor discharged); `refinedDeepInputKinds_eq_original` rfl linkage; AbsTopIII01LogShell, 07/08/09 green modules, 10StatementLedger, 11IndexIds, 12AssetMap.
- **Missing layer:** gate L6 deep input — paper-scope precise definitions + required construction (named class-B); currently list-of-strings interface.
- **Paper-faithful extension steps:** (1) restate DeepInput fields as precise Props with paper line refs; (2) expose typed consumer interface to IUT IV §1 / L8 display; (3) no proof attempt until user opts; (4) keep AbsTopIII05 as named input row (never consume as proved).
- **Reusable assets:** AbsTopIII05RefinedActual, AbsTopIII01 log-shell, 07/08/09 modules, 10/11/12 ledger/index/asset-map, hull probes.

## E-2 H5 O^x + det/tensor bookkeeping

- **Existing closures:** `Hull09H5GapsActual` 5405B: hull09_scalingUnits_subset_hull, hull09_hull_eq_closure, hull09DetTensorBookkeeping_exponent, hull09_ray_mem_iff (PROVED framing).
- **Missing layer:** H5 full O(-)^{-1} normalization + hull<=image-volume inequality (named); SG3b tensor Haar product blocker (no actual product-Haar formula; exact first error; no fake packet).
- **Paper-faithful extension steps:** (1) replace typed hypotheses in Hull11/Hull13 consumer with hull09 lemmas; (2) write paper-scope O^x stabilization statement; (3) prove product-Haar formula per paper or register exact named gap; (4) no L8 wiring until premises real.
- **Reusable assets:** Hull09H5GapsActual, Hull11/Hull13 consumer interfaces, S3132VFormScalingReduction, hull probes.

## E-3 H7 / Ob9 arbitrary-iterate bound

- **Existing closures:** `Hull08Ob9LogLinkActual` 5921B: HullOb9Inputs, hull_ob9_interface, hull_ob9_repClass_congr PROVED; `Hull12Ob9BoundTransferActual` one-sided transfer/interface; `Hull13` two-sided bound 5260B sha 79F714C0 probe_ok (upper projection).
- **Missing layer:** full H7 arbitrary-iterate bound DEEP CLASS-B NAMED (L6); both-sided bound still named.
- **Paper-faithful extension steps:** (1) replace HullH7Ob9ComparisonInputs fields with typed Props linked to Hull08 interface; (2) expose both-sided bound as named Prop with exact paper line; (3) record one-sided vs both-sided status; (4) no L8 wiring until named premise typed.
- **Reusable assets:** Hull08Ob9LogLinkActual, Hull12Ob9BoundTransferActual, Hull13 consumer, Hull09 gaps framing.

## E-4 EtTh realization deeper rows

- **Existing closures:** `EtTh11ThetaRealizationRowsActual` 4337B PROVED rows (theta/elliptic power-kernel mono, modLThetaProjection_surjective, modLThetaToElliptic); EtTh12/13 PROVED rows; `Mzk1EtThRealizationConsumerActual` CITABLE 14/11293B sha C12C6CAC probe_ok (11-row inventory: 3 named + 8 proved; conditional wiring).
- **Missing layer:** scheme-level realization/corollary rows class-B (L7); no portable asset; qpilot rows pending.
- **Paper-faithful extension steps:** (1) enumerate which EtTh11/12/13 theorems feed L8 route (typed consumer file); (2) mark scheme-level named rows with paper lines; (3) qpilot realizations assessed only after typed consumer; (4) no gate row.
- **Reusable assets:** EtTh11/12/13, EtThRealizationConsumer, theta power-kernel monotonicity lemmas.

## E-5 IUT IV §1 uniform height-vs-volume inputs

- **Existing closures:** S3171IUTIVSection1StatementActual 4742B, EstimatesActual 2879B, InputsActual 3351B, DisplayActual 6921B, UniformHeightConsumer; `coord/FOUNDATIONS-IUTIV.md` 16984B (stepxi inventory).
- **Missing layer:** (b) UndilatedHeightBound + (c) UndilatedRegionBound named; height dictionary != height-volume inequality (S2802); C3 region formula not actual (S2826); Cor312 reduces to S2717UpperGap (S2804).
- **Paper-faithful extension steps:** (1) turn S3171 inputs into typed Prop list with paper lines; (2) exact statement of uniform height-vs-volume; (3) connect UniformHeightConsumer to Hull11/13 hypotheses; (4) no L8 wiring until named premises typed.
- **Reusable assets:** S3171 statement/estimates/inputs/display, FOUNDATIONS-IUTIV.md, S2717/S2802/S2804/S2826 assets.

## E-6 H6 precise/toOld (mostly resolved)

- **Existing closures:** Mzk1GeometricCorePreciseActual 7/4025B F19EEEC7 probe_ok; Mzk1GeomCorePreciseToOldActual 9/7043B 1FA662D1 probe_ok; D-BASE Mzk1GeomCoreFoundationActual 14032B 0F74F433 CITABLE 15 probe_ok (RR-independent pencil base); RR Mzk1RRProvedActual 3/4757B B3A67DEE probe_ok; RRInterface Mzk1RRInterfaceActual 9/8895B 7BD88E7D probe_ok.
- **Missing layer:** GenEll15 precise existence class-B; H6 gate layer wiring; remaining D-RR: Foundation flt_core migration + hdual discharge + ell_sub_single_add_one + zero_divisor_exists_proved.
- **Paper-faithful extension steps:** (1) migrate Foundation to flt_core; (2) discharge hdual; (3) ell_sub_single_add_one; (4) zero_divisor_exists_proved against real RR; (5) replace Hull11H6 inputs by precise witness + prove hull11_h6_upgrade from GenEll15 precise statement; (6) no gate row until GenEll15 precise existence honest.
- **Reusable assets:** precise/toOld actuals, Foundation pencil base, RR proved/interface, Hull11 precise consumer.

## E-7 deep consumer support files

- **Existing closures:** Mzk1HullEInputsActual 9/8093B 2DC5ABD3 probe_ok (H5/H7 named deep inputs as explicit structure params -> GenEll Cor312 intermediate conditional assembly); Mzk1P1ConsumerDeepInputsActual 11/8734B 10CAC8F2 probe_ok (P1 consumer named inputs typed).
- **Missing layer:** typed premise wiring into consumer chains; no closure claims.
- **Paper-faithful extension steps:** (1) make each named input a typed Prop structure linked to paper lines; (2) wire into consumer design; (3) record pins for each green file; (4) no gate row.
- **Reusable assets:** Mzk1HullEInputsActual, Mzk1P1ConsumerDeepInputsActual, P1 consumer design.

## Not-yet / excluded from gate (policy)

- All E items remain named/class-B/conditional; NO gate rows until their foundation objects are stable and Lead approves a separate revision.
- C/D/E gate exclusion remains (A409/A410): this document is planning only.

Prepared by lattice under Lead A426; skeleton for merge with mainline E-EXISTING-CLOSURE-MAP later.


---

## MERGE COMPLETE (mainline A428)
- Mainline deliverable `coord/E-EXISTING-CLOSURE-MAP.md` (16KB + qpilot A426 cross-reference) is now on disk; merge checklist items (1)-(5) satisfied: closure pins reconciled, paper line refs per item, named vs proved marked, no proof claims, no gate rows.
- E mapping headlines merged: (E-1) AbsTopIII01-14 all EXIT0+olean (AbsTopIII05Section0Objects being edited); refined D1-D4; paper gaps Prop5.8(i)(ii)/Cor5.5/Section-0 algorithms remain named (new theory; no assets). (E-2) Hull09 framing; LogShellFrobeniusPower/Consumer/General/P2Boundary + KappaOrbit unit files real; H5 O(-)^{-1} normalization + hull<=image-volume + tensor Haar product remain named. (E-3) Hull08/12/13 + two-sided framework; both-sided arbitrary-iterate named. (E-4) Example36* real (19374/50169B); HaarTranslate LogFrobenius + HullDeterminant matrixLogDet; EtTh00-13 all EXIT0; EtTh02 ten deep named + EtTh11 rows5-7 named; consumer CITABLE 14. (E-5) IUTIV Section1/2 + ArithmeticDivisorDegree/Archimedean/Different/StepV real; SourceUnitRegionHaarData/IQCarrier/Cor312GapReduction:306; (b)/(c) named; S2717UpperGap single analytic endpoint (S2804); no L8 wiring.
- CORRECTION to E-6 line above: D-RR remaining items are now DISCHARGED: `Mzk1GeomCoreRRProvedActual` EXIT0 15877B sha 813224A5 CITABLE 14 probe_ok, `zero_divisor_exists_proved` with NO named inputs (hRR=functionFieldRiemannRoch_proved, hdual=flt_core ell_eq_zero_deg_neg + canonical bound + punctureDivisor=|T|; flt_core root only) => D-RR BOTTOM; D remaining = scheme<->function-field bridge + finite map construction layer (legacy flt_test Foundation retained for scheme layer due flt_th deps).
- C NY-2 correction: `Mzk1NestedInductionStepProviderActual` 5647B sha CD14AEB3 CITABLE 8 probe_ok: f0Map/f0Map_comp/stepSetP real; `stepTransport_of_goal` conditional on named `CVCompositionLawF`; geometry f1/f2/f4 PROVED; CVCompositionLawF + fixed-beta + P1 measure completion named.
- Expansion order (aligned with qpilot A426, asset-first): 1 build OddThetaNegativeDecay/TermAlgebra; 2 build AbsoluteKummer*/SourceThetaPilotIQContainment; 3 SourceLogShellDatum -> Prop5.8(ii) concrete diagram layer; 4 finish Section0Objects; 5 Example36 Frobenioid boundary <-> EtTh05/11 rows; 6 Prop5.8(i)(ii)/Cor5.5 algorithmic parts = named new theory.
- No gate edit; GATE NOT PASSED; binding HOLD; L8 FROZEN; FINAL PIN V150@18248/CFC6CE08; registry 14041.
### E-5 EDGE UPDATE (A432)
- FOUNDATIONS-IUTIV.md extended to 27163B (A426; REAL closure R1-R19 / MODEL-IFACE M1-M5,I1-I9 / extension plan); SKELETON-IUTIV-ABCBRIDGE.md 17349B + skeleton-iutiv-abcbrige-edges.tsv 25128B (178 rows) delivered (stepxi A429); citable probe _FOUNDATIONS-IUTIV-CitableProbe EXIT0 results:210254.
