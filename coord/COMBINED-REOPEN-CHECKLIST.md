# COMBINED REOPEN / RE-PIN CHECKLIST (S3140 acceptance package, 2026-11-10)

**Rule (Lead):** the frozen baseline is gate `S3140ClosureGateActual` (SIZE 22809,
src F5CF23EB… / olean 4E8DFE7F…, olean 03:43:38) + frozen registry
`S3131FinalResidualRegistryActual` (SIZE 12847, src 76809A6D…, olean 03:41:17) +
acceptance record `S3140FinalAcceptanceRecordActual` (SIZE 13087, src B08AD7A0… /
olean 618E8E04…). The registry reopens ONLY when a REAL residual actually closes,
with ONE combined reopen + ONE single re-pin. No gate-v4 promotion without a
SEPARATE explicit audit. Do not re-pin for non-gate-dep changes or note-only churn.

## 1. Reopen triggers and required evidence (any ONE of these)

| # | candidate closure | owner | required evidence | reopen scope |
|---|---|---|---|---|
| 1 | F4.a `S3135ValueMonoidIdentification` / `S3135ValueGroupDegreeCompatibility` | abc | citable theorem/construction + trio probe; residual genuinely discharged. **A12:** the compatibility lemma is NOT derivable from `SourceImageRealization` (only arbitrary `posRealAction` hom + `degree_of_q` at log q): it is a NEW source datum (degree faithfulness, IUT III Rem 3.9.4(iv)) OR can only be closed BY CONSTRUCTION in task-72's from-scratch model (documented MODEL closure, not general) — a reduction alone (`S3135ValueGroupCompatibilityActual`) is NOT a closure | registry note F4.a resolved (general only if a general construction; model closure stated as such); audit citation |
| 2 | M2a (R1 `valued_coe_rat` presentation bridge) | qpilot | EXIT=0 file with REAL declarations closing the bridge + trio probe (NOT doc-only) | registry note M2a CLOSED; R1 = M1 + M2b; audit citation |
| 3 | nontrivial F4(b): new `SourceUnitRegionHaarData` with scaling = genuine Z_5-unit z ≠ 1 + `S3135CompletionBaseFieldUnitScalar z` + μ(λ·O)=μ(O) | abc | instance fields satisfied; `S3135ScalingLogDegreeZero` proved NON-definitionally (via multiplicativity/logDegree, not scaling=1); self-similarity/set equality proved; trio probes. **A13 (proof-level obstruction, abc audit):** over the FROZEN model, unit-in-hull + nonpositive value monoid force `scaling = 1` (0 = s+y with y≤0 & s≤0 ⇒ s=0), and the concrete value monoid has a TRIVIAL unit group ⇒ NO nontrivial-scaling record exists over the frozen model; the input-fidelity flag is upgraded from "absence" to STRUCTURAL FORCING. Repair is possible only via task-72's model design (value monoid with genuine unit group, symmetric O ≠ hull, explicit nontrivial z). A trivial `z ≠ 1` in a changed model must still be checked for genuine nontriviality | registry note F4(b) nontrivial case realized only if a task-72 model record exists (documented model object, NOT frozen tree object); input-fidelity wording update; audit citation |
| 4 | C3 convention `SourceInd1ConventionIdentification` | stepxi | FULL identification constructed/proved (current `S3139C3ConventionTheoremActual` = constructible half only, residual REMAINS → NOT a trigger) | registry note C3 convention resolved; audit citation |
| 5 | F4.b index `S3135LogShellScalingIndex` | abc | citable index computation + trio probe | registry note b1 index closed |
| 6 | GATE V4 | abc/mainline | NOT a reopen trigger under current ruling. Separate requirement: circularity + input-fidelity audit of v4 hb (concrete-only so far) BEFORE any gate import/promotion | separate audit + explicit Lead approval |

## 2. Evidence gate per trigger (mandatory, no exceptions)

1. `tools/xif_citable_check.ps1 -File <file> [-Probe <probe>]` verdict **CITABLE**
   (EXIT=0 last line, fresh olean, REAL declarations, trio/no-axiom probe, no sorryAx).
2. Semantic check that the residual actually closes: not a rename, not a trivial
   instance, not a doc-only file, not concrete-model evidence claimed for the
   general paper carrier. For nontrivial F4(b): z must be a genuine Z_5-unit ≠ 1,
   and scaling log-degree 0 must be derived from multiplicativity/log-degree
   properties (not by `rfl` from `scaling := 1`).
3. No new hypothesis/axiom introduced; `#print axioms` trio-only (or no-axiom rfl).

## 3. One combined re-pin procedure (after mainline's registry note edit is frozen)

1. mainline edits ONLY the registry notes for the real closure, rebuilds, and sends
   "REGISTRY FROZEN AT <size>" with exact size/sha/olean mtime; **no other edits**.
2. Touch (mtime-only) + append: `S3140ClosureGateActual`,
   `_S3140ClosureGateAxiomsProbe`, `_S3140FinalAxiomRecountProbeActual`,
   `S3140FinalAcceptanceRecordActual`.
3. Verify: gate olean mtime > frozen registry olean mtime; all 41 direct imports
   fresh; recount 53 = 50 trio + 3 no-axiom, zero sorryAx (report if decl set changed).
4. Update acceptance record: real-closure note + audit citation (M2a note only if
   M2a truly closed; F4(b) wording only if nontrivial instance verified).
5. Run `xif_citable_check.ps1` on gate (+probe), record, audit; update
   `coord/FINAL-ARTIFACTS-20261110.md` hash rows; append ledger entry; notify
   Lead/mainline/hull/lattice with the exact new gate src/olean pair + registry size.
6. Re-freeze and re-record the baseline here.

## 3b. task-72 from-scratch skeleton verification commands (when it lands)

```powershell
# (a) citable + probe
pwsh -NoProfile -File tools/xif_citable_check.ps1 -File <skeleton>.lean -Probe <probe>.lean
# (b) genuinely explicit definitions, no placeholders
Select-String <skeleton>.lean -Pattern '^(opaque|axiom|constant|instance .*:.*sorry)|sorry|admit|True|PUnit'
Select-String <skeleton>.lean -Pattern '^(structure|def|instance) '   # fields instantiated?
Select-String <skeleton>.lean -Pattern 'placeToMod|bad|C3|SourceFmod|SourceCapsuleFiber'
# check every definition is a real := term, not a hypothesis binder
Select-String <skeleton>.lean -Pattern '^\s*\(' | Select-String -Pattern 'place|mod|C3|fiber|isom'
# (c) definitional closures not circular/trivial
Select-String <skeleton>.lean -Pattern ':= rfl|:= by rfl|exact h|= target|:= target'
```

Manual semantic check: the place map / placeToMod / bad↔C3 data must be constructed
from existing explicit structures (completion, prime strips, Fmod, capsule labels),
NOT assumed as a hypothesis/field that merely restates the residual; any `rfl`
closure must be a genuine computation (e.g. a projection/instance field), not a
restatement of an assumed equality. Only then may it count as a real closure and
trigger the combined reopen.

## 4. Abort / stop conditions

- File is doc-only/comment-only, EXIT=1, stale olean, or probe not trio → NOT a closure.
- Residual renamed/weakened or new hypothesis introduced → stop, report to Lead.
- Any suspicion of circularity or concrete-model leakage → stop the reopen and run a
  targeted audit first (cf. `S3140CircularityAuditActual`).

## 5. Current candidate status snapshot (2026-11-10 03:57)

- M2a: `S3133M2aClosedActual` EXIT=1 (pending fix; 6 decls but not green) — NOT closed.
- M1 donor: `S3137M1ConcreteDonorActual` EXIT=1 — pending.
- hull concrete source canonical residual: `S3132ConcreteSourceCanonicalResidualActual` EXIT=1 — pending.
- C3 convention: `S3139C3ConventionTheoremActual` EXIT=0 CITABLE, but constructible
  half only; `SourceInd1ConventionIdentification` REMAINS → NOT a trigger.
- F4.a: `S3135ValueGroupCompatibilityActual` EXIT=0 CITABLE (4 decls) reduces F4.a to
  ONE compatibility lemma `S3135ValueGroupDegreeCompatibility` (Prop, NOT proved);
  `S3131F4aDegreeIdentityActual` gives only a NECESSARY degree identity. F4.a is
  therefore a REDUCTION, not a closure — reopen trigger requires the compatibility
  lemma itself proved/constructed (or supplied by a from-scratch model).
  **A12:** the compatibility datum is a NEW source datum (IUT III Rem 3.9.4(iv)),
  not derivable from `SourceImageRealization`; only a task-72 model construction may
  supply it, and that would be a documented MODEL closure (not the general claim).
- V4 candidate: EXIT=0 but explicitly NOT promoted (concrete-only hb caveat).
- abc nontrivial-scaling instance: SHELVED per Lead (user: explore route first);
  **A13 proof-level obstruction recorded**: over the frozen model, nontrivial scaling
  is STRUCTURALLY IMPOSSIBLE (unit-in-hull + nonpositive value monoid + trivial
  concrete unit group ⇒ scaling = 1), so the input-fidelity issue is a structural
  forcing, not a missing record; repair only via task-72 model design. Cross-check
  procedure (a)-(d) remains prepared if a task-72 model record appears.
- **task-72 (qpilot lead, from-scratch concrete model) MONITORING:** when the
  skeleton lands, verify (i) `xif_citable_check.ps1` CITABLE (real decls + probe),
  (ii) place data / `placeToMod` / bad↔C3 definitions are GENUINELY EXPLICIT and not
  abstract placeholders (no `opaque`/`axiom`/`constant`, no "assume the place map"
  hypothesis standing in for the construction; structure fields actually
  instantiated), (iii) any claimed "definitional" closure is not circular/trivial
  (e.g. the construction must not be defined in terms of the target residual, and
  `rfl`-closures must not merely restate an assumed hypothesis). Only a real
  construction of the remaining residual (compatibility lemma / place data) may
  trigger a combined reopen.

## 6. C3 CONVENTION CLOSURE - CERTIFIED (2026-11-10 04:05), awaiting combined reopen

- Artifact: S3139C3ConventionClosureActual EXIT=0 SIZE=5576 (src 69D16A41... / olean 91648 1428941E..., fresh); theorem sourceInd1ConventionIdentification_holds : forall {l}{V} (I) (A), SourceInd1ConventionIdentification I A (NO extra hypotheses).
- Probe: _S3139C3ConventionClosureAxiomsProbe EXIT=0 SIZE=986 (src 0CC4FB93... / olean 5C62CA93..., fresh); xif_citable_check CITABLE (3 real decls, probe_ok true); kernel trio/no-sorry on closure theorem, comparison theorem, manufactured tool piTensorEntryPermute_tprod, and production laws (polyIsoOfPerm_tensorMap_tprod, PrcAutomorphismTensorAction_tprod).
- Non-circularity: target name absent from Ind1AutomorphismTensorActionActual and the generic tool; action = PiTensorProduct.reindex; proof composes proved laws only.
- Reopen scope (Lead-approved pending): ONE registry note marking FT.C3.convention-identification PROVED/CLOSED + audit citation; 15 ids/order/ABC unchanged; re-freeze; SINGLE gate re-pin + recount + record update + FINAL-ARTIFACTS.
- Status: waiting for mainline REGISTRY FROZEN AT <size>, then execute single re-pin.


## 7. THIRD COMBINED REOPEN — model-route closure (checklist prepared 2026-11-10 04:49)

**Status: NOT OPEN. Pins locked at gate 23066 / registry 13129 / record 15501; 2 reopens
consumed; NO reopen/re-pin before complete evidence + explicit Lead GO.**

Evidence required (all must be EXIT=0 + real declarations + CITABLE + trio/no-sorry probes):
- (a) model package fields PROVED definitionally in the assembled from-scratch model
  (no cross-monoid equalities/assumptions; inspect binder lists/proof terms);
- (b) M1 in-model explicit placeToMod wired (S3137ModelPlaceToModWiringActual CITABLE:
  modelPlaceToModDataS3135 ofDistinct with rfl images + injectivity) and consumed by the model;
- (c) M2b definitional descent (qVFamily := model q; rfl-level, no cross-object assumption);
- (d) F4.a / F4.b by construction via the two named lemmas
  s3135_valueMonoid_realified_identification, s3135_procession_scaling_unit_degree_zero
  (elementary; unit-log-zero derived non-definitionally);
- (e) in-model R1 composition (R1 = M1 + M2b discharged; M0/M3 proved citations);
- (f) full checker evidence (xif_citable_check CITABLE) + trio/no-sorry probes.

Reopen scope (after Lead GO): ONE narrow registry note only (model-route closure;
abstract-contract wording unchanged; F4.c.cardP stays the single ABC-strength residual;
paper route (b)/(c) remain class B), then ONE gate re-pin + probes + recount + record/
FINAL-ARTIFACTS/ledger update + notify all. No v4 promotion.

Artifacts: S3150ThirdReopenChecklistActual (CITABLE), ModelRouteAuditCriteria,
ThirdReopenScope, ModelEvidenceStatus, ThirdReopenPins, MilestoneI.
Current evidence status: (b) available/CITABLE; F4.b unit-log-zero shape available;
value data/unit factor available; (a),(c),(d),(e) PENDING.

