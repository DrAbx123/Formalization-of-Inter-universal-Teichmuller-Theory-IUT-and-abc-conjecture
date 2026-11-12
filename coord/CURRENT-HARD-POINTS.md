# CURRENT HARD POINTS (handoff brief, 2026-11-10 ~20:35 Asia/Shanghai)

Purpose: hand this to another model/engineer so they do NOT duplicate work. All paths relative to `D:\lean`.

## 0. Project context
- Formalizing IUT 3.12 prerequisites from the three axioms (propext, Classical.choice, Quot.sound), no sorry/extra axioms/True-toy.
- Lean 4 + Mathlib pinned at v4.32.2 (rev 905b9581); compile: `lake env lean -R D:\lean -o <rel>.olean <rel>.lean` from `D:\lean`.
- Main paper files live in `tmp/sheaf/xif/paper/*.lean`; registry pins are FROZEN at 14041 / gate 23066 / record 18800.
- Team owners: stage4 (terminal gate file), abc (2.4 StepProvider), stepxi (h22 binding, S1b done), hull (H6/GeometricCore helpers), mainline (ledger/gate), lead (coordination).

## 1. PRIMARY BLOCKER: full `mzk1Lemma22_fullShape_gate`
File: `tmp/sheaf/xif/paper/Mzk1Lemma22ConditionedActual.lean` (currently ~13335 B, EXIT=1 while stage4 edits; an earlier 2054 B version containing only the H-preservation packaging is green/CITABLE).
Required theorem (exact name expected by downstream binding `Mzk1Thm25UnconditionalActual`):
```lean
theorem mzk1Lemma22_fullShape_gate :
    ∀ (S : Finset (P1Point ℚ)) (β : P1Point ℚ),
      Lemma22Hypotheses S β → Mzk1Lemma22FullShape S β
```
What is ALREADY GREEN and consumable (all fresh EXIT=0 + checker CITABLE, probe trio):
- `Mzk1Lemma22HypPreservationActual` — components 1–4: `target_zero_mem`, `target_infty_mem`, `target_positivity`, `target_beta_notin` (avoids), plus Even-n helpers.
- `Mzk1Lemma22HypPreservationSeparationActual` — `hyp_separation` (component 5). 9136 B, sha C86E19B8.
- `Mzk1Lemma22HypPreservationCanonicalActual` — `canonical_hypotheses_preserved` (all five components assembled), 4111 B.
- `Mzk1Lemma22ConditionedActual` (2054 B green variant) — `hyp_preservation_full`, `hyp_preservation_of_hypotheses`.
- `Mzk1GChoiceDataOfHypothesesActual` — `gChoiceData_of_hypotheses`, `stepExists_of_hypotheses` (the induction-step witness; 3062 B, sha 99CBD8C0).
- `Mzk1Lemma22InductionActual` — `mzk1Lemma22_partial_induction` (|S| strong induction principle, 4 decls).
- `Mzk1GChoiceCardActual` — `card_image_gPoly_lt` (cardinal descent).
- `Mzk1PolyChainRuleActual` — `polyMapPoints_comp_finite/infty`, `polyUnramifiedAt_comp_finite/infty`.
- `Mzk1PolyUnramifiedCompositionActual` — `polyUnramifiedOver_comp`.
- `Mzk1Lemma22StatementShapeActual` — `Mzk1Lemma22FullShape`, `fullShape_to_partial`.
- `Mzk1P1MorphismInterfaceActual`, `Mzk1PolyMapActual`, `Mzk1GChoiceScaleActual` (v5), `Mzk1GChoiceConstructActual` (gPoly/eval/collapse), `Mzk1GChoiceAvoidActual`.

What is MISSING (this is the hard Lean-engineering part):
(A) Base case: `Mzk1Lemma22FullShape S β` for `|S| ≤ 3` via linear maps:
   - S={0,∞}: X or 2X; S={0,α,∞}: C α⁻¹ · X; prove nonconstant + PreservesSet into {0,1,∞} + AvoidsPoint β + UnramifiedOver (elementary).
(B) Polynomial-level strong induction on |S|: given IH for smaller cardinal, compose `gPoly D` (from `Mzk1ScaleData.ofHypotheses`) with the IH polynomial map, using:
   - `hyp_preservation_of_hypotheses` to re-establish hypotheses on (g(S), g(β)),
   - `card_image_gPoly_lt` for cardinal decrease,
   - `polyMapPoints_comp_finite/infty` and `polyUnramifiedOver_comp` for map/unramified composition,
   - package via `Mzk1Lemma22InductionStep`/`mzk1Lemma22_partial_induction` and `gChoiceData_of_hypotheses`/`stepExists_of_hypotheses`.
(C) Goal transport: `Mzk1Lemma22FullShape` clause types (`PreservesSet`/`AvoidsPoint`/`UnramifiedOver`) must be transported through the composition.

Current concrete Lean errors while attempting this (line numbers in the 13335 B version)`:`
- 107:10 unsolved goals; 109:6 `simp` made no progress
- 122:6 `simp` made no progress
- 143:10 invalid rewrite: pattern is metavariable (?m.37)
- 196:10 type mismatch after simplification
- 229:8 `simp` made no progress; 240:12 metavariable rewrite; 265:12 type mismatch; 273:8 simp no progress; 278:12 metavariable rewrite; 297:17 unsolved goals
These are tactic-engineering issues (coercions `Finset (P1Point ℚ)`/`↑S`, `polyMapPoints` images, dependent `Mzk1ScaleData` fields), not missing math.

Downstream consumer once this lands:
- `tmp/sheaf/xif/paper/Mzk1Thm25UnconditionalActual.lean` (pre-written, 3823 B) imports this file and binds `thm25_of_lemma24_and_geometricCore` → **Thm 2.5 unconditional** (modulo named `Lemma24Shape` + `Mzk1GeometricCoreRecast`). The binding is HELD until the gate is green.

## 2. SECONDARY: [Mzk1] Lemma 2.4 paper-obligation residues
Everything else is green/audited: (G)(F)(D)(M) interface evidence, L2.3 normalization (numeric + transfer), rational base case, nested assembly `mzk1Lemma24_assembly` (real well-founded recursion), BaseProvider (ℚ→ℂ lifted, GREEN), separation, StepProvider S1a + S1b now PROVED.
Remaining:
- `tmp/sheaf/xif/paper/Mzk1Lemma24StepProvider2Actual.lean` (2992 B) — measured fresh EXIT=0 by watchdog, but its probe `Mzk1Lemma24StepProvider2ProbeActual` currently errors with unknown identifier `Mzk1Lemma24StepProvider2Actual.s3135_goal_transport` (probe/adapter mismatch). Needs: (i) confirm what S2/S3 it really proves; (ii) update `Mzk1Lemma24StepProviderActual` status/route to consume `fieldDegreeDrop_proved` (S1 complete, from stepxi's `Mzk1Lemma24ValueDegreeDropActual`, 5107 B, sha CFC8FF3E); (iii) then `mzk1Lemma24_assembly` + providers = paper 2.4 obligation.
- If StepProvider2 is only wiring/statement, the genuinely missing piece is (S2) point-level measure decrease for S' = f0(S ∪ S0) and (S3) transport composition.

## 3. Other named residuals (not on terminal path)
- H6 PARTIAL: GeometricCore deep input (precise schema now in place, NOT proved); is a named hypothesis in Thm2.5 wiring.
- `belyi_pair` analytic/topology port: deferred (Mathlib API drift; mechanical part fixed). Non-gate.
- Several ported (non-gate) files still red in queue (belyi_pair residual, tauceti_rr ZPowers, flt_th functionFieldRiemannRoch copies) — do NOT spend effort on these; they are not needed.

## 4. Coordination (avoid duplication)
- stage4: owns `Mzk1Lemma22ConditionedActual.lean` (full gate).
- stepxi: owns `Mzk1Thm25UnconditionalActual` (binding; HELD) and did S1b.
- abc: owns `Mzk1Lemma24StepProvider2Actual` (S2/S3) + StepProvider status.
- hull: helper files done (`Mzk1Lemma22HypPreservationCanonicalActual`, `Mzk1Lemma24BaseProviderActual`, True-stub fixed); available for integration.
- Do not edit files owned by others without coordination; the repo uses a watchdog compile queue (`tools/xif_guarded_queue.ps1`) and a citable check `tools/xif_citable_check.ps1 -File <rel> [-Probe <rel>] -Root D:\lean`.

---

## AUTHITATIVE CORRECTIONS (2026-11-10 20:47, from user/external review) — supersedes paths above

### A. The old full-gate path is INVALID
- `mzk1Lemma22_partial_induction`: base/stepExists are unconditionally quantified over all (S,β) (InductionActual:61); for β∈S conclusion false ⇒ premises unobtainable; produces abstract P1Morphism, cannot return to ℚ[X]. `stepExists_of_hypotheses` loses "φ=gPoly and H holds on image".
- `comp`: ratFunc := ψ.ratFunc * φ.ratFunc is a PRODUCT not composition (CompositionActual:29); comp(polyMorphism g)(polyMorphism h) ≠ polyMorphism (h.comp g). The "goal transport by structural rewriting" (C) is impossible; the three predicates depend only on .mapPoints.

### B. Replacement design (flattened polynomial induction)
```lean
def Good (f : ℚ[X]) (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop :=
  1 ≤ f.natDegree ∧ (∀ p ∈ S, polyMapPoints f p ∈ specialSet) ∧
  polyMapPoints f β ∉ specialSet ∧ CritIn01 f
-- induction: ∀ n S β, S.card ≤ n → Lemma22Hypotheses S β → ∃ f, Good f S β
```
- Good→FullShape is an anonymous constructor (PreservesSet/↑S/setOf are defeq; no simp/rw).
- β in quantifier (it becomes g(β)); H in proposition.
- Existence lemma wraps Mzk1ScaleData OUTSIDE the induction:
  `∃ g, 1 ≤ g.natDegree ∧ (S.image g).card < S.card ∧ Lemma22Hypotheses (S.image g) (g β) ∧ critical values of g ⊆ g(S)`;
  assembled from gPoly_natDegree_pos, card_image_gPoly_lt, hyp_preservation_full, gChoice_unramified; D.S ≡ S is rfl; do not rw/simp on D (H's type depends on S).
- Composition lemma: ∞ branch vacuous (∞↦∞); finite branch h(g x) ∉ {0,1} ⇒ g x ∉ g(S) ⇒ g′(x) ≠ 0, then IH. gChoice_avoids not needed (already component 4 of H′).
- Base case unified f = C c * X (derivative constant c, unramified automatic): no case analysis on S, no b=1 branch. posRatS_card ⇒ (posRatS S).card ≤ 1; empty: c = 2/b; nonempty: c = a⁻¹ (uniqueness Finset.card_le_one; c·b ≥ 2 via hsep_of_hypotheses).
- Known concrete error roots in stage4's file: ofFinite/some vs ↑S/S are only defeq → use show/exact; :45-46 obtain consumes H; :115/:210/:251 missing Finset.mem_coe; :175/:241/:277 show f.derivative.eval x ≠ 0 directly; :148/:158 ha orientation reversed.

### C. Unramified strength fix (nearly free)
Current UnramifiedOver only quantifies p : P1Point ℚ, but paper Lemma 2.1(b) is about x ∈ ℂ (paper:59). Fix:
`CritIn01 f := ∀ z : ℂ, aeval z f.derivative = 0 → aeval z f = 0 ∨ aeval z f = 1`
(belyi21_derivative_root is already over ℂ; FullShape derived as corollary, target unchanged).

### D. §2 Lemma 2.4 target is DEGENERATE
`Mzk1Lemma24Goal` has targetSet/unramifiedAt as ∃ and P1Morphism.mapPoints unrelated to ratFunc ⇒ Goal S β ⟺ β ∉ S (witness mapPoints := id, T := ↑S). Reverse direction false: mzk1Lemma24_assembly conclusion includes β∈S states, cannot satisfy μ premises. So StepProviderStatement (∀μ, constant (1,0)), BaseProviderStatement, Lemma24Shape (targetSet = ∅) are FALSIFIABLE and S2/S3 wiring closes nothing. Must restate: Sφ ⊆ P¹(ℚ), φ(β) ∈ P¹(ℚ)∖Sφ, critical values ⊆ S_φ, induction with invariant, fixed μ.
### E. The gate has NO real consumer
`thm25_wiring` conclusion uses only hcore (Wiring:129); h22/h24 are just stored in the record. `Mzk1GeometricCoreWitness` three conditions are free Prop fields (RealStructure:59). So binding Thm2.5 "unconditional" changes no mathematics. The real consumer is the P¹-case composite 2.4∘2.3∘2.2, requiring 2.3's Möbius (not expressible at polynomial level).
### F. Shared invariant for 2.2 and 2.4
Drop pointwise unramifiedAt; carry "critical value set ⊆ target". It satisfies CV(ψ∘φ) = ψ(CV φ) ∪ CV ψ, which is exactly what paper 2.4's merging f0(S0) into S′ uses.

### G. Status policy
- "binding = Thm2.5 unconditional" narrative SUSPENDED; gate NOT PASSED; binding HOLD indefinitely until restated target + real consumer land.
- Existing green assets (S1a/S1b/S2/S3/S2-i, BaseProvider, HPRES 1–5, L2.3, assembly) remain valid as lemmas but must be re-wired under the corrected targets; they do not constitute paper-obligation closure under the degenerate target.
