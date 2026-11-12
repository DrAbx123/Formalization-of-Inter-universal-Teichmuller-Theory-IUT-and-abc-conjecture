# FINAL ARTIFACTS — S3140 / IUT formalization acceptance package (2026-11-10)

**Status: POST-THIRD-CLOSURE PIN (three real residual closures folded).** The C3
convention (first), M2a (second) and Option-B model-route (third) residuals are
CLOSED; the acceptance package is re-pinned against the reopened frozen registry
`S3131FinalResidualRegistryActual` EXIT=0 **SIZE 14041**, src sha256
`4AF7EC606B9A38659F9BE3558F9F36D24BC80BB5F78382DE59AB9AC488FD7B65` (src mtime
05:20:04, olean 05:20:15 sha `5991A075…`; ONLY delta = narrow Option-B
R1/model note, 15 ids/order/ABC unchanged). Gate `S3140ClosureGateActual`
EXIT=0 **SIZE 23066** (src `7A903654…`, olean 05:23:30 > registry olean
05:20:15); acceptance record `S3140FinalAcceptanceRecordActual` **SIZE 18800**
(src `0667D25F…`, olean 46352 `EBF0B0FC…`, 05:27:35). Gate probe + recount
probe rebuilt fresh (05:26:13 / 05:26:14; recount 53=50+3, zero sorryAx).
15 ids/owners order/length/ABC unchanged; F4.c.cardP unchanged; abstract-contract
M1/M2b (class B/C) + paper-route (b)/(c) wording unchanged; NO gate-v4
promotion. **USER DIRECTIVE (binding): registry stays FROZEN at 14041 — no
further reopen/re-pin cycles; the next reopen is only for a PAPER-LEVEL theorem
((b) uniform height-vs-volume comparison, (c) RegionRelativeToHullAndWeight +
hull/region volume, or a full Cor 3.12 quantitative split). Meanwhile only
ledger/checker/FINAL-STATUS evidence updates (doc-only, no reopens).**

Workspace: `D:\lean`. Protocol: append files to `tmp/xif_guarded_queue.txt`;
watchdog compiles; citable = EXIT=0 in `tmp/xif_guarded_results.log` + fresh
olean + `#print axioms` footprint only [propext, Classical.choice, Quot.sound];
verify with `tools/xif_citable_check.ps1 -File <f> [-Probe <p>]` (real
declarations required; doc-only/log parsing is NOT evidence). **Watchdog
limitation:** dependency changes never re-trigger a consumer compile — touch the
source mtime and re-append; verify target olean mtime > key dependency olean
mtime (TOOL-INVENTORY G).

## 1. Final acceptance pair (post-second-closure)

| artifact | src bytes | sha256 (src) | olean bytes | olean mtime |
|---|---|---|---|---|
| `tmp/sheaf/xif/paper/S3140ClosureGateActual.lean` (project closure gate) | 23066 | `7A90365426ACB93DFC7AC429414823F76A27AFEDC03A44A3729574591F9F2191` | 28320 | 05:23:30 |
| `tmp/sheaf/xif/paper/_S3140ClosureGateAxiomsProbe.lean` (2 gate theorems trio + C3/M2a closure checks) | 1756 | `2E8F9B1C3508CB580C09DABFD9C0462338DBF6B031CE0A21974D054EA5047527` | 2280 | 05:26:13 |
| `tmp/sheaf/xif/paper/_S3140FinalAxiomRecountProbeActual.lean` (kernel recount 53/50/3/53) | 21460 | `89B52AF76FC015611A542EA6379E7B095D7F002031E797D7807077FF55446C24` | 341664 | 05:26:14 |
| `tmp/sheaf/xif/paper/S3140FinalAcceptanceRecordActual.lean` (acceptance record; C3+M2a+Option-B folded, A12/A13, verification rule) | 18800 | `0667D25F374976FF661DE2DE54CAFA91AA3A7A0297106A2D8DEBF85862CDA58B` | 46352 | 05:27:35 |
| `tmp/sheaf/xif/paper/S3140CircularityAuditActual.lean` (task-68 strict circularity audit; NO proof circularity) | 8005 | `6B8898344C004B6660F9D6024BB6D68473F66693064181A2AF8A265F48BE9F35` | 43536 | 03:51:41 |
| `tmp/sheaf/xif/paper/S3131FinalResidualRegistryActual.lean` (frozen 15-residual registry, 14041) | 14041 | `4AF7EC606B9A38659F9BE3558F9F36D24BC80BB5F78382DE59AB9AC488FD7B65` | 125768 | 05:20:15 |
| `tmp/sheaf/xif/paper/S3139C3ConventionClosureActual.lean` (C3 CONVENTION CLOSED; sourceInd1ConventionIdentification_holds) | 5576 | `69D16A4138477179ED9792F77E9B553CEEC9C2200D871045781854CFB76DEF0D` | 91648 | 04:03:26 |
| `tmp/sheaf/xif/paper/_S3139C3ConventionClosureAxiomsProbe.lean` (C3 closure kernel probe) | 986 | `0CC4FB934F99510E21C0ED608F7E52E457A93EC7BAF587B5A875995890F0DF4B` | 2424 | 04:05:05 |
| `tmp/sheaf/xif/paper/S3139ToolsPiTensorEntryPermute.lean` (manufactured Mathlib-gap tool used by C3 closure) | 2429 | `56F814CA2DA289018F3B9F66E451A7649BF6CA91183CA1F93959A24C3678274E` | 57176 | 03:56:59 |
| `tmp/sheaf/xif/paper/S3133M2aClosedActual.lean` (M2a CLOSED: norm=5^-1 + canonical Gaussian q-norm + isometry transport) | 5173 | `30E910B2C6A729721927BD7D38FC0CEB5731DD079B8BBD89ADAF1D6A4C6C9669` | 72344 | 04:0x |
| `tmp/sheaf/xif/paper/S3133M2aNormReductionActual.lean` (M2a norm reduction support) | 3200 | `6B08130333CD5D4EF5261F54B2A7F159984CB43816127535B55080013C71FE21` | 58640 | 04:0x |

Gate theorems: `s3140_projectClosureGate` (three final-gate residuals =>
`ABCConjecture`) + `s3140_projectClosureGate_tight`; axiom gate **53 = 50 trio
+ 3 no-axiom**, zero sorryAx; 41 direct imports all fresh; gate olean 04:08:11 >
registry olean 04:06:14. C3 closure: theorem
`sourceInd1ConventionIdentification_holds : ∀ {l}{V} (I) (A),
SourceInd1ConventionIdentification I A` (NO extra hypotheses); all involved
declarations trio-only/no-sorry; `xif_citable_check` CITABLE (3 decls,
probe_ok); non-circular (target name absent from action/tool definitions;
action = PiTensorProduct.reindex; proof composes proved laws only).

Olean sha256 (key): gate `4E8DFE7F1522AEE45775CF383123D1169E2F2AB0DA8C9AB6753F872EE76F34EE`;
gate probe `EEF05E9B8FD8BD0F4194E1F351E135069D6BAE18BB18C0A4AB7190A519B2803F`;
recount probe `92D9E0F28E8B1BFEFBB0E748B59161B2423209B8E3DDCE31BAA638B4F1665B98`;
acceptance record `EBF0B0FCECBBAAC20AD786D95A33D822B079F54E54BC34D26AE1B57125E333E9`;
registry `5991A0750B116361046ADFA0694F0FFD2FA0C07809B7256001CFD61E777D9B34` (14041 build);
M2a closure `0DE537B54B13779BF904A7574BBBB8E5E4D15B712125A981F3DB6A309DF238BA`
+ norm reduction `DD5AEA434B17BB7C8609273B0A67B210F490C40CDA06A018942982E8C914830C`; C3 closure
`1428941E27A4B21947FE64FAF8152378853D02DBEF735401B192B30A7FA167CD`;
C3 probe `5C62CA9347FC701CAD82D00B7BF15B5A929C4FEA1E0846E053C4FA37F6AC4D2A`;
C3 tool `6CC1361D8B473665F81D2DE9C81F32C50EADFF8B37076A3F82CA62C3EC595249`.

### 1.1 Third-closure (Option-B model route, V=Unit) certified evidence

| artifact | src bytes | sha256 (src) | olean bytes | evidence |
|---|---|---|---|---|
| `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean` (tree concrete model: Family:322/OriginalInput:346/Data:416) | 22486 | `7595ADD0D7D59B51DDCCB0C4860889FD5DFDD678F00AA820C626E72D491404B4` | 681064 | built lib, olean fresh |
| `tmp/sheaf/xif/paper/S3133ExistingModelAdaptationActual.lean` (adaptation: M1 in-model constructible + M2b definitional) | 5504 | `7A0678538BDE2D54714F65A21D2573593EC2BFE5EDFCA62BC608E11DA619E4A6` | 89000 | EXIT=0, checker CITABLE 9 decls, probe_ok |
| `tmp/sheaf/xif/paper/_S3133Batch37AxiomsProbe.lean` (adaptation probe) | 534 | `20B78AB97FF35CCCCC841786F23321300FDA50F2AB98AB0E5475ECF829F6299C` | 2280 | EXIT=0 trio |
| `tmp/sheaf/xif/paper/S3135ModelSkeletonInterfaceActual.lean` (baseUnit=-1 witness: norm 1, (-1)*(-1)=1, mu((-1)*O)=mu(O)) | 7974 | `328039CAAF1469E122974781A2824D980C348E8C1C41A7C241E9DC0DB1421C5D` | 206920 | EXIT=0, checker CITABLE 6 decls, probe_ok |
| `tmp/sheaf/xif/paper/S3135ModelBaseUnitProbeActual.lean` (witness probe) | 454 | `7AE5EA213C0255E139568AD6F5E01488F7A1F6EE8EA55D945124725D24E80D4A` | 2312 | EXIT=0 trio |
| `tmp/sheaf/xif/paper/S3135RealifiedIdentificationActual.lean` (F4.a class-B data) | 2079 | `99D87EB8B5579FEF18A29C5E09304DF27F6395E981065E509EA5174359FD8840` | 28192 | CITABLE 2 |
| `tmp/sheaf/xif/paper/S3135ProcessionUnitDatumActual.lean` (F4.b class-B data) | 2412 | `4FECDFAC6D4ADFA39DC70C7A4BC43423381556D4EE38207931C82D5F0D45FF9A` | 26624 | CITABLE 2 |
| `tmp/sheaf/xif/paper/S3135F4BothByConstructionActual.lean` (F4.a+F4.b by construction) | 2159 | `266CE85D88B42373E3391C168274139651905277FD1FE5B0384B9ACE77AB6E8B` | 33688 | CITABLE 1 |
| `tmp/sheaf/xif/paper/S3135ModelScalingPairActual.lean` (generic scaling pair) | 1643 | `17CDA584F0B2F97DDB15B0B60ED847533AEA87FA1FB51D5B1F23A63E54AD2B61` | 97840 | CITABLE 3 |
| `tmp/sheaf/xif/paper/S3135ModelMuEqualityShapeActual.lean` | 2394 | `080136C08213DA347DF1F31C58EC5B15B7DEBD1100D4B39030A44EE78195AD89` | 43368 | CITABLE 1 |
| `tmp/sheaf/xif/paper/S3135ModelUnitRegionInstanceActual.lean` | 3176 | `D2442AD51346CCBB3F817120339DB9E76725BCE63DF6AF384C9383F131A1856F` | 60680 | CITABLE 2 |
| `tmp/sheaf/xif/paper/S3135ModelHaarUnitMassActual.lean` | 1838 | `9BC6DE02F446E20D7F14EBC87205A3509D5372EA132F04497AD9F0F7869C8AEC` | 28064 | CITABLE 2 |

Audit: real declarations; NO assumed equalities/cross-monoid assumptions; no
doc-only counted. EXCLUDED (not evidence): Sum-V superseded files
(S3133ModelVBasis/FPrimeStrip/HodgeTheater/ThetaPacketValue/Source31Data/
InModelR1/M2bDescent), parked doc-only S3133ModelTheaterFamilyActual (831B, 0
decls), retired S3137ModelTheaterPrimeStripData, WITHDRAWN
S3135ModelBaseUnitActual. Registry-note evidence row recorded in
`S3160RegistryNoteEvidenceRowActual`; frozen evidence list in
`S3160OptionBFrozenEvidenceListActual`.

## 2. Registry support files

| artifact | src bytes | sha256 (src) |
|---|---|---|
| `tmp/sheaf/xif/paper/S3131RegistryGateOwnersActual.lean` (root owner dict, length 15) | 1221 | `1D4395679692B5131492EBB52FE7821E7B7A05DBA63895194E3458051C6CD525` |
| `tmp/sheaf/xif/paper/S3131RegistryLengthActual.lean` (root length = 15, rfl) | 486 | `A6B35ADF6D1ECC113007191EADBF908ABB6EB655EE5E42F4266D83591A3F5DEC` |
| `tmp/sheaf/xif/paper/S3131RegistryABCStrengthActual.lean` (root ABC list = [F4.c.cardP-ABC-strength]) | 648 | `A0F0506D03FEB14E997B3D59DB67B4E8112AF443F5907CD6C532F28F9C022B89` |
| `tmp/sheaf/xif/paper/S3131RegistryProbeActual.lean` (registry probe) | 309 | `3257365E82217CCBBDF296148FBB38FFC5FB93639A5E0500D929C823ACD86D54` |
| `tmp/sheaf/xif/paper/S3131FinalAcceptanceSummaryActual.lean` (mainline acceptance summary) | 2953 | `512AB0596B522010461D6BE4B1FECACBBBC9B7D20636BAB05375C5F7C67712BF` |
| `tmp/sheaf/xif/paper/S3131FinalAcceptanceProbeActual.lean` (summary probe) | 188 | `1213737728E79EA4B84797F8CD2419727AC9BF6D1E4F3D7055F91BAD9DEEBD3F` |

## 3. Strongest-theorem artifacts (with probes)

| artifact | src bytes | sha256 (src) | probe |
|---|---|---|---|
| `tmp/sheaf/xif/paper/S3131CanonicalRootedQCActual.lean` (mainline canonical Q_C/H_C; unconditional signed comparison = IUT III Cor 3.12 :10352) | 4055 | `B3F9E2CD2245D328008F5A29D84CB0E42EFCC3FD0A297AC9910F0AD25138624B` | `S3131CanonicalRootedProbeActual.lean` |
| `tmp/sheaf/xif/paper/S3134MainlineRootedHFaActual.lean` (shehdd canonical H_C consumers + Step 3115 comparison) | 13581 | `BAE27354783C49DB107C85551ED12827ACE7347AAAC451789C8C418476080D56` | `_S3134MainlineRootedHFaAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3134LastSeamExactMissingActual.lean` (last-seam exact missing composition) | 12110 | `9224BC3B0D9DD83EA45723E07D2B106929B640E9EFAB6FCBA94C9C2555AD2453` | `_S3134LastSeamExactMissingAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3134FourthTriangleCompositionStatusActual.lean` (actual composition (hull+det) o dsc(SHE)) | 11706 | `854C524BFAA6070D8D4C8A30DA5BB13561842EC6B1935BC6E55CDF1EFE733C1A` | `_S3134FourthTriangleCompositionAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3135FinalAssemblyGateActual.lean` (strongest conditional F4/F5 gate; carrier+hpt+hzero+hP) | 9256 | `3A766555A6003D2AB1D2CA1DD8C42BFDEC783CC816207A768D7AF524F316B933` | `S3135FinalAssemblyGateProbeActual.lean` |
| `tmp/sheaf/xif/paper/S3135FinalAssemblyGateV3Actual.lean` (V3 final assembly gate) | 5683 | `7D4A596AFFAFC0F4FC356346D0D40F174DC482E755C4F70C72F199E3F4D86586` | covered by gate probe |
| `tmp/sheaf/xif/paper/S3134CanonicalQFormulaGapActual.lean` (explicit numeric Q_C gap alias) | 4125 | `22F105A86CDD98BDF4F797B438DEBC4A6E318CC6693F4CF0E4A2F85D61398921` | `_S3134CanonicalQFormulaGapAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3132Task30ThetaHalfActual.lean` (hull Task-30 Theta-half reductions) | 8248 | `94601D8DF31FBAA558859ECBF17C8FE9562295A1C83FCEB43E17BFF5934F2C01` | probe in hull stream |
| `tmp/sheaf/xif/paper/S3137SameCModelMapResidualActual.lean` (lattice canonical R1 model-map residual) | 8727 | `942B857B01FB3B51B10FB148588FFA0066B790F25F26C26F5F8F996C85AE9C7C` | `S3137R1RegistryCanonicalAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3140NormalizationChannelToolActual.lean` (manufactured generic normalization-channel tool, 5 theorems) | 4265 | `07E64302ABB03765A24BB78E4E5612BBF3922C9CC970C8AF65FFC567556D738D` | `_S3140NormalizationChannelToolAxiomsProbe.lean` |
| `tmp/sheaf/xif/paper/S3140HaarExtToolProbeActual.lean` (Haar/Riesz tool cross-check for abc F4.b1) | 1887 | `DC31D7E73F7102407766A20999E2C1070EC0B74656F0D985614EFAEC2A076E0D` | self (Mathlib-only) |
| `tmp/sheaf/xif/paper/S3140ThetaNormalizationLegActual.lean` (raw Theta => V-form => task-30 Theta half => ray) | 7467 | `01C987D19C1494F9AC2A86A0FFB71E720B502AF6A1278EA4C4EC09BB2B0345E3` | `_S3140ThetaNormalizationLegAxiomsProbe.lean` |

## 4. Project documents

| document | bytes | sha256 |
|---|---|---|
| `AUDIT_LEDGER.md` | 2174666 | `13BCCC1C926A07E3030A3CAF99F22791E06714065F65AE986E9AF3C69F0A5113` |
| `coord/TOOL-INVENTORY.md` | 28712 | `D24B44F4B35D20963AB2BD2BE917C4D9E7E059F6CF5225E05A57560C983EF3DD` |
| `coord/FINAL-STATUS-20261110.md` (mainline final-status doc) | 54610 | `7C31A0A772123DEA954F9B771E89AB67055B88449271016C4028001735A8A116` |
| `coord/COMBINED-REOPEN-CHECKLIST.md` (one-reopen/one-re-pin procedure) | 12203 | `AE08D26E8DA6136450C083323E90348BB0D643CD8AC3BDAC31251156B9625962` |

## 5. Verification recipe

1. Append the gate; confirm EXIT=0, fresh olean, olean mtime > registry olean mtime.
2. All 41 direct imports fresh (olean mtime >= src mtime).
3. Axiom gate: 53 declared = 50 trio + 3 no-axiom, zero sorryAx.
4. Kernel recount: recompile `_S3140FinalAxiomRecountProbeActual` (rfl facts 53/50/3/53).
5. `tools/xif_citable_check.ps1 -File <gate> -Probe <gate probe>` = CITABLE.
6. Only then update this index + record + ledger; ONE reopen + ONE re-pin per real closure.
7. **USER DIRECTIVE (binding, post-third-closure): registry FROZEN at 14041 — no
   further reopen/re-pin cycles. Next reopen ONLY for a PAPER-LEVEL theorem:
   (b) uniform height-vs-volume comparison, (c) RegionRelativeToHullAndWeight +
   hull/region volume, or a full Cor 3.12 quantitative split. Until then only
   ledger/checker/FINAL-STATUS evidence updates (doc-only, no reopens).**

## 6. Residual-watch protocol

- **Gate-dependency set** = the 41 imports + oleans; any change invalidates the pin.
- **On a gate-dep change from a REAL closure:** ONE combined reopen (registry note only,
  by mainline) + ONE re-pin (gate + gate probe + recount probe + acceptance record),
  recount, record/index/ledger update, notify all.
- **Non-gate-dep changes:** no re-pin; ledger/index notes only.
- **Registry freeze rule (updated by user directive):** FROZEN at SIZE 14041;
  no v4 promotion; the NEXT reopen/re-pin is authorized ONLY by a paper-level
  theorem — (b) uniform height-vs-volume comparison, (c)
  RegionRelativeToHullAndWeight + hull/region volume, or a full Cor 3.12
  quantitative split. Doc-only evidence updates (ledger/checker/FINAL-STATUS)
  do NOT reopen.
- **VERIFICATION RULE (mandatory):** EXIT=0 + fresh olean + ACTUAL declarations (not
  comment/doc-only) + trio/no-axiom probe; use `tools/xif_citable_check.ps1`;
  false greens recorded (stale gate 21906; doc-only M2a 147613).
- **CIRCULARITY AUDIT (task-68):** `S3140CircularityAuditActual` verdict = NO proof
  circularity in the V3 gate closure; V4 candidate needs separate audit before promotion.
- **APPENDIX A12/A13:** A12 — F4.a compatibility is a NEW source datum (IUT III Rem
  3.9.4(iv)), model-closure only via task-72 (not general); A13 — frozen-model
  structural forcing: unit-in-hull + nonpositive value monoid + trivial concrete unit
  group force scaling=1, so no nontrivial-scaling record over the frozen model
  (repair only via task-72 model design). Checklist: `coord/COMBINED-REOPEN-CHECKLIST.md`.
- **TWO REAL RESIDUAL CLOSURES FOLDED IN:** (1) C3 CONVENTION CLOSED
  (`S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds`, CITABLE,
  trio/no-sorry, non-circular; registry 13108); (2) M2a CLOSED
  (`S3133M2aClosedActual` + `S3133M2aNormReductionActual`, both EXIT=0 with real
  declarations and checker CITABLE; R1 = M1 + M2b; registry 13129). Doc-only false
  green (M2a 147613) remains recorded under the verification rule.
- **PRIOR-ART INVENTORY (reuse rows; Lead §7.9 repo-first):**
  `SourceUnitRegionHaarDataActual.lean` (22486B; prime-strip/theater family:122/143,
  links/laws:213/224-284, injectivity:288, Family:322, OriginalInput:346 — CORE model
  prior art), `IQCarrierConcreteModel.lean` (34217B; concrete IQ carrier model),
  `CardAMPLThetaBoundSupply.lean` (12977B; hull/AMPL theta-bound assets),
  `HunitEpsilonTransferReduction.lean` (13938B; normalization/scaling transfer),
  `IUTIV/Estimates` (`Section1.lean` 13808B, `Section2.lean` 27185B incl. [GenEll]
  reduction refs, `ArithmeticDivisorDegree.lean` 94950B,
  `StepVProcessionAverage.lean` 12974B — IV estimate layer, class B formalization
  targets). RULE: report 'prior art: file:line decl -> reuse/adapt/none' before every
  new Lean file; never re-prove existing results.
- **Watch items after this pin:** R1.M1 remains OPEN (bad<->C3 tensor-index
  equivalence + base-place equality); R1.M2b exact spec `S3133M2bTateQIdentification`;
  abc F4(b) nontrivial case (A13 structural forcing; task-72 model design only) /
  GATE V4 (future explicit reopen, requires separate audit); lattice INDEX 52/47
  data-only; task-72 model value package RED (needs real model construction);
  hull fiber data-only `ActualPlaceDataForC3`; model-route option audit: Option A
  (V=S3135ModelV) NOT certifiable (parked/doc-only + prime-strip red), Option B
  (V=Unit) CLOSEST pending `S3133ExistingModelAdaptationActual` green (currently
  EXIT=1; 9 decls). Pins locked 13129/23066/15501.
