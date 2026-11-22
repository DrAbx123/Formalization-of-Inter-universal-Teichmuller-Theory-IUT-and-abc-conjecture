# R6 / R4.1 crosswalk + R5/R7 shapes + M4 G2 verification (sophie, 2026-11-18)

Purpose: map (R6.1)-(R6.3) and R4.1 to exact Lean statements/types, with the PINNED
citations (no fake IV lines), and record the R5 SeparationInput B(p,d) shape and R7
same-L/same-y requirements.  M4 G2 verification status at the end.

## 1. R6.1: local Weil function bound `h_E <= m h_{O(1)}`

Lean (DONE): `tmp/sheaf/xif/paper/Mzk1HTF4R6Actual.lean`
- `structure R6LocalWeilData` fields:
  `n : ℕ`, `n_gt_three : 3 < (n:ℝ)`, `m : ℕ`, `hO1 : ℝ`,
  `hP : ℝ`, `hP_nonneg : 0 <= hP`,
  `hE : ℝ`, `hE_eq : hE = (m:ℝ)*hO1 - hP`,
  `hOmega : ℝ`, `hnorm : (m:ℝ)*hO1 = (m:ℝ)/((n:ℝ)-3)*hOmega`;
- `R6LocalWeilData.hE_le_m : D.hE <= (D.m:ℝ)*D.hO1`;
- `R6LocalWeilData.hE_le_kappa : D.hE <= (D.m:ℝ)/((D.n:ℝ)-3)*D.hOmega`;
- `R6LocalWeilData.ofProjHeight` (concrete from `x : ι → K`, multi-coordinate,
  `hP := Height.logHeight x`, `hP_nonneg := Height.logHeight_nonneg x`).

Citations (pinned; see `coord/R6-PAPER-LINES-DOC.md`):
- IV L2557: "... is the **local height** of E_F [cf. **[GenEll], Definition 3.3**] ..."
  (the literal `h_E <= m_i h_{O(1)}` / `m_i/(n-3)` lines are in the EXTERNAL [GenEll]
  local-height section; NOT in repo IUT texts);
- route L566: `h_ω + h_E <= (1+η)(D(L)+h_E) + C`;
- route L569: `(1-ηκ) h_ω <= (1+η)D(L) + C`;
- route L576: `h_ω(y) <= (1+δ)D(L) + C_{n,d,δ}`.

## 2. R6.2: `h_omega` comparison

Lean: `R6LocalWeilData.hnorm` is an EXPLICIT field; `ofProjHeight` sets
`hOmega := (n-3)*hO1`, making it an identity (wired, not a scheme-side identification).
Citation: route L566/L569 (both are the h_ω/h_E comparisons); paper-side literal is
[GenEll] Def 3.3 (external).  The identification `hOmega = (n-3) hO1` with the actual
ω-height/metric is an OPEN crosswalk (the per-place metric item below).

## 3. R6.3: `h_E` identity (divisor height of reduced E_i)

Lean: `R6LocalWeilData.hE_eq : hE = m*hO1 - hP` (explicit, not an identification).
Remaining crosswalk (OPEN): `hE = deg_{O(1)}(E_i)` (divisor height of the reduced E_i
via completion-to-degree m_i); plus `Mzk1HTF4R6GeneratorsActual` donors:
`R6GeneratorData`, `R6PlaceData`, `sum_lambda` (finite homogeneous generating family).
Citation: route R6 row (P7 route table: "同一数域/多截面：h_E 有限齐次生成元、base
divisor=E_i、lambda_{E_i,v}、h_E<=kappa h_omega; R6.1-R6.3") + [GenEll] Def 3.3 for the
local height; no literal IV line for the m_i/(n-3) normalization.

Crosswalk to close R6 end-to-end:
1. completion-to-degree `m_i`: `hP` = Height.logHeight of completed generators of degree
   `m_i` (scheme completion map);
2. scheme `baseDiv`: `hE_eq` tied to the divisor of reduced `E_i`;
3. per-place metric: `hOmega` tied to local ω-height/metric in CΘ (IV L1365-1376 shape).

## 4. R4.1: protected-point / noncritical map

Lean (per route table): emmy's `Mzk1G1R4ProtectedActual` (route A: layer1 + structures)
+ `Mzk1G1F2H1VanishingDataActual` (H1 vanishing, built on
`coord/R4-H1-VANISHING-DATA-DOC.md`); henry's `Mzk1G1R44RationalRecursionActual`
(`M2AnalyticTargetRat`).
R4.1 statement shape: psi is a noncritical map on the protected finite branch set,
satisfying R4.1; the H1 side consumes `H1VanishingData.h1_vanish`
`(∀ D, indexOfSpecialty D = 0)` + `constantsAreBase`.
Citation: route R4 row ("一般受保护点 noncritical map（三路线取一，出口 psi 满足 R4.1）；
§6.4 有理函数递归") — paper-line pin for the protected-point criterion is the
[GenEll]/D1 local-height section (same external block as R6); no fake IV line.

## 5. R5: SeparationInput B(p,d) shape

Route §7.1 lines (authoritative):
- L428: 通用局部域现在只补 SeparationInput 的实际实例;
- L430: UniversalSeparationToUFLEActual 仍接收 SeparationInput;
- L437: "选**对所有 m<=d** 有效的 `B(p,d)`。不能直接以 `d(v_p(d)+1)` 替代
  `m(v_p(m)+1)`，因为 `v_p` 不单调。可取有限最大值，或先用保守的 `d(d+2)`.";
- L439: 填入 SeparationInput 后调用 explicit N / coefficient finite-ization / Krasner /
  universal field assembly.
Base different=0: fill the local instance from `differentIdeal_self_eq_top` (base field
different ideal is top), NOT as a prerequisite (route §7.1 context).

## 6. R7: F7 three classes + `D(L) <= log rad(abc) + C_n` (same L, same y)

Route §9.1 lines:
- L584: F7 task = actual field ramification instance;
- L586: existing donors (fermatRoot / minpoly degree bound / global discriminant sum /
  tame count upper bound / wild normalized algebra) cannot directly give F7 for the
  actual fermatLiftL;
- L594: 按实际素数分三类 (three classes of primes);
- L602: **`D(L) <= Σ_{p | abc} log p + C_n`**;
- L613: 对每个三元组，使用 9.1 的同一个 L 和同一个 y.
Also route L82 `D(L) = log|disc L|/[L:Q]`; L273 `h̄_L(λ) <= (1+η)(D(L)+N_L(λ)) + C`;
L345 `D(Ftpd)+N_Ftpd(λ) <= D(L)+N_L(λ)`.

## 7. M4 G2 verification: `5•P=0 ↔ evalDivisionPolynomial` (against route §5.2(2))

Status: **PENDING exact file/decl name from grace** (no file in the tree currently matched
`evalDivisionPolynomial` / `5 •` / `G2`).  Verification criteria (route §5.2(2)):
1. the polynomial must be the REAL `legendreΨ₅` (division-polynomial recursion), not an
   arbitrary polynomial;
2. the point (x,y) must satisfy the Legendre curve equation `y^2 = x(x-1)(x-lam)`;
3. `5 • P = 0 ↔ legendreΨ₅.eval x = 0` must be proved for actual points of the curve
   (currently the tree has `Mzk1G1F2ThetaTorsionCoordsActual`
   `three_nsmul_eq_zero_iff_lnAtPoint_three_eq_zero` /
   `ln_three_eq_zero_iff_three_nsmul_eq_zero` for n=3, donor
   `EllipticDivisionPolynomialEvaluation.ln_eq_eval_preΨ_of_odd`; n=5 needs the division
   polynomial zero criterion, S1373 only covers 2 and 3, Mathlib only 2);
4. completeness (#E[5] = 25, enumeration) has no donor;
5. field: x∪y generated field = actual 5-torsion field has no donor.
⇒ If the G2 statement is only `5•P=0 ↔ eval ψ₅ = 0` **for points already known to be
5-torsion**, it does not close route §5.2(2) ④⑤; it must at least use the real ψ₅ and the
curve equation (③), leaving ④⑤ explicit.  Report exact names when grace lands them.

### M4/G2 status update (2026-11-18 16:34)

grace's `Mzk1G1F2ThetaTorsionFiveYActual` is **DONE 16:34:35**. Exact names:
`exists_sq_eq_complex`, `legendreYOfX`, **`legendreYOfX_sq : (y)^2 = x(x-1)(x-λ)`**,
`fiveTorsionCoords (lam) : Set (ℂ × ℂ) := {(x,y) | eval x ψ₅ = 0 ∧ y^2 = x(x-1)(x-λ)}`,
`mem_fiveTorsionCoords_iff`, `ln_of_root`.

Verification against route §5.2(2): **step ② is closed** (real ψ₅ roots + y satisfying the
Legendre curve equation). **③④⑤ remain OPEN** and are honestly declared in the file header:
- ③ needs `DivisionPolynomialZeroCriterion 5` (and n = l), i.e.
  `∀ P, n • P = 0 ↔ ψₙ(P) = 0`; absent from Mathlib and from S1373 (only n = 2, 3);
- ④ enumeration completeness (`#E[n] = n²` and equality with the constructed set): no donor;
- ⑤ field generated by x ∪ y equals the actual torsion field: no donor.
⇒ No mismatch.  The M4 claim must stay at step ②; the G2 statement
`five_nsmul_some_eq_zero_iff` (henry) is still PENDING; when it lands, check that it uses
the real `legendreΨ₅` and the curve equation (③) and does not silently assume ④⑤.


## NEW DONE exact names (2026-11-18 17:05-17:07)

- **R0.2 crosswalk** (sophie, DONE 17:05:44):
  `Mzk1ULR02CrosswalkActual.{R02CrosswalkData, R02CrosswalkData.cPFullFiber_nonneg,
  R02CrosswalkData.crosswalk'}` with fields `cPFullFiber/cP_local/fmodLocalDegree/dMod/
  dMod_pos/crosswalk`.  david's companion: `Mzk1ULR0CrosswalkActual.{CPlocalCrosswalk,
  CPlocalCrosswalk.eq, CPlocalCrosswalk.mul}`.
- **R3 torsion field** (grace, DONE 17:05:45): `Mzk1G1F2ThetaTorsionFieldActual.
  {fiveTorsionCoordSet, fiveTorsionField, root_mem_fiveTorsionField,
  legendreYOfX_mem_fiveTorsionField}` — step ⑤ (field generated by x∪y coordinates)
  partially addressed (field = adjoin of coord set); torsion-membership/③④ remain open.
- **R7 F7 degree** (andrew, DONE 17:06:01): `Mzk1G1F7LiftDegreeActual.
  {isIntegral_fermatRoot, finrank_adjoin_singleton_le_of_pow_eq,
  fermatLiftL_finiteDimensional, **fermatLiftL_finrank_le_sq : finrank ℚ (fermatLiftL n hn a b c)
  <= n*n**}` — matches route §9.1 R7 requirement `[L:Q] <= n^2`.
- **R5 different bound conservative** (DONE 17:06:01):
  `Mzk1G1DifferentBoundConservativeActual.{differentBoundConservative (d) := d*(d+2),
  padicValNat_le_self, differentBound_le_conservative, differentBoundConservative_pos}`
  — exactly route §7.1 L437's conservative `d(d+2)` choice for B(p,d).
- **R4.4 rational recursion** (henry, DONE 17:07:26): `Mzk1G1R44RationalRecursionActual.
  {M2AnalyticTargetRat, polyEvalP1_eq_polyMapPoints, specialSet_eq,
  m2AnalyticTargetRat_of_lemma24Target}`.

### R4.4 verification vs route §6.4 (rational map, not polynomial)

Route §6.4 (L410-424): "受保护值的 Belyi 递归：**使用有理函数，不强求最终为多项式**";
"推荐将中间对象升级为实际 P¹→P¹ 的 rational map；原定的 noncritical scheme morphism 目标
并未要求多项式" (L412).  Henry's `M2AnalyticTargetRat (S₁ β) : ∃ φ : P1Morphism ℚ,
φ.nonconstant ∧ (∀ p∈S₁, φ.mapPoints p ∈ specialSet) ∧ φ.mapPoints β ∉ specialSet`
uses `P1Morphism ℚ` (a rational map on ℙ¹), NOT a polynomial, and specialSet = {0,1,∞}.
=> **MATCHES route §6.4** (rational map; nonconstant; Branch values into the boundary
specialSet; protected point β avoids it).  Note: route L424 also names a set T; the current
statement uses a single protected point β (equivalent when T = {β}) — if T is a general
finite set, add the corresponding pointwise avoidance (minor parameterization extension).


## STATUS UPDATE 2026-11-18 17:45-17:48 (R3 / F7 corrections)

### R3 torsion (grace) - current state
- `Mzk1G1F2ThetaTorsionCoordsActual` **FAIL 17:48:47 (no log file)** — infra/stale state, not a
  code verdict; its declarations are still only n = 3: `threeTorsionX`,
  `evalDivisionPolynomial_legendre_three`, `legendre_three_nsmul_eq_zero_iff`,
  `legendre_evalDivisionPolynomialAtPoint_three_eq_zero_iff`; NO n = 5/l zero equivalence yet.
- `Mzk1G1R3TwoNsmulXActual` **DONE 17:45:14**: `two_nsmul_some_x` (x-coordinate of 2•P via
  Mathlib addition formulas) — partial route §5.2(2) addition-formula evidence (for 2-torsion
  doubling), NOT the 5•P=0 zero-equivalence G2.
=> Route §5.2(2) ③④⑤ remain open for n=5/l; the missing donor is still
`DivisionPolynomialZeroCriterion 5` (and l); enumeration completeness (#E[n]=n²) and
torsion-field equality have no donor.

### R7 F7 - CORRECTED status (supersedes the 17:06 DONE note)
- `Mzk1G1F7LiftDegreeActual` **FAIL 17:45:33** (error at `hy : y^m = (algebraMap K L) q`);
  the earlier 17:06:01 DONE version is **reverted/superseded** — do not cite it as current;
- `Mzk1G1F7LiftTowerActual` **FAIL 17:45:07 (Type mismatch at line 26)** until Import/type fix;
- `Mzk1G1F7LiftActual` **DONE 14:22:04** (still valid).
=> R7 docstrings must cite only `Mzk1G1F7LiftActual` (DONE) + route §9.1 lines; the
`LiftDegree` `[L:Q] <= n^2` item and `LiftTower` are currently FAIL pending fixes.


## UPDATE 2026-11-18 17:55: F7 corrected status + R4 psi_structure evidence

### F7 (R7) - CORRECTED (authoritative)
- `Mzk1G1F7LiftActual` **DONE 14:22:04** - the ONLY currently valid F7 item;
- `Mzk1G1F7LiftDegreeActual` **FAIL 17:45:33** (`hy : y^m = (algebraMap K L) q` statement
  issue); the 17:06 DONE version is reverted - do not cite;
- `Mzk1G1F7LiftTowerActual` **FAIL 17:45:07** (Type mismatch at line 26) - import/type fix
  required.
=> R7 docstrings cite `Mzk1G1F7LiftActual` + route §9.1 L584-613 only.

### R4 psi_structure evidence (emmy's R4ProtectedActual)
`Mzk1G1R4ProtectedActual.ProtectedPointData` fields: `S T : Finset (Place K F)`,
`D : Divisor K F`, `s0 s1 psi : F`, `h_S_notMem_T`, `h_T_subset_supp`,
`h_supp_subset_T`, `h_supp_disjoint_S`, and `psi_structure` = route §6.2(iv) in
consolidated form: `psi⁻¹(0) = supp D`, `0 ∉ psi(S)`, `0 ∉ Branch psi`.
Supporting declarations: `suppSet`, `mem_suppSet`, `sectionOrder`, `pointDivisor`,
`pointDivisor_apply_of_mem/notMem/ne_zero_iff`, `pointDivisor_support/effective/reduced`,
`fiberAboveZero`, `unramifiedOverZero`.
NOTE (root split): the file lives on the `flt_core` root; the four
`tmp.external.ported.flt.Definitions.*` imports cannot be mixed in one file, so the
`flt_core` mirrors are used instead (identical decl names/lines: `ConstantsAreBase`:48,
`indexOfSpecialty`:139, `RiemannIndexFormula`:23, `WeilDualityAdelic`:28,
`weilDuality_of_riemannIndex_of_adelic`:59, `ResidueTheorem`:110).

### 2026-11-18 18:02 tails: R3 Mzk1G1R3LegendrePsi2TwoActual NO-EVENT (psi2AtTwo_eq_two_mul_addY / ne_negY_of_a1a3 / psi2AtTwo_mul_cube; verify on DONE). F7: LiftDegreeBasic DONE 18:00:32 but lacks fermatLiftL_finrank_le_sq; LiftDegree FAIL; LiftTower FAIL; only LiftActual DONE. R5: SeparationInput/SeparationToUFLEConsumer NO-EVENT (queued); noncircular signature stands.
### 2026-11-18 18:02 TorsionCoords DONE: Mzk1G1F2ThetaTorsionCoordsActual DONE 18:02:32 (n=3: threeTorsionX / evalDivisionPolynomial_legendre_three / legendre_three_nsmul_eq_zero_iff / legendre_evalDivisionPolynomialAtPoint_three_eq_zero_iff; source clean, no sorry/axiom; log rotated so axiom triad not re-read). n=5/l ③④⑤ still OPEN. F7: LiftDegreeBasic DONE 18:00:32 lacks finrank_le_sq; LiftDegree/Tower FAIL. R5: SeparationInput/Consumer NO-EVENT.
### 2026-11-18 18:08 batch audit: R5 Mzk1G1SeparationInputActual FAIL 18:04:42 (real FAIL, log present); SeparationToUFLEConsumer NO-EVENT -> R5 conditional, no instance. F7 LiftDegreeBasic source now has finrank_le_sq (stale olean, recompiling). KHP5Bridge docstring fixed (stale olean). Infra wave 22+30 failures 18:05-18:08 not code verdicts.
### 2026-11-18 18:09: R3 FiveNsmulX DONE 18:09:11 (four_smul_eq_two_smul_two / five_smul_eq_four_smul_add / five_smul_some_eq; addition-formula side, zero criterion still absent). R7 LiftDegreeBasic re-DONE 18:09:13 WITH fermatLiftL_finrank_le_sq -> [L:Q]<=n^2 recovered.
### 2026-11-18 18:12: all three recompiles consistent (mtime < DONE): FiveNsmulX 18:09:11, F7LiftDegreeBasic 18:09:13 (finrank_le_sq present), KHP5Bridge 18:12:16 (fixed docstring). Infra wave 18:13-18:15 heavy-file failures not code verdicts.

### 2026-11-18 18:30-18:32 R5: MonogenicMinpolyBridge DONE; Separation chain re-queued

- **`Mzk1G1MonogenicMinpolyBridgeActual` DONE 18:30:05** (clean, no sorry; latest axiom
  print `[propext, Classical.choice, Quot.sound]`):
  **`exists_minpoly_data : ∃ (x : M) (e : M ≃ₐ[ℚ_[p]] IntermediateField.adjoin ℚ_[p] ({x} : Set M)),
  IsIntegral ℚ_[p] x ∧ ‖x‖ ≤ 1 ∧ (minpoly ℚ_[p] x).natDegree = Module.finrank ℚ_[p] M`**
  -- the AlgEquiv monogenic-generator/minpoly bridge for R5 (uses
  `nonempty_monogenicIntegers` + `adjoin_eq_top_of_fractionRing`).
- `Mzk1G1SeparationInputActual` FAIL 18:31:53 = **infra** (`.olean.private`:
  `Mathlib/LinearAlgebra/Determinant`), the earlier 18:04:42 FAIL was due to the then-missing
  `Mzk1G1MonogenicMinpolyBridgeActual.olean` (now DONE);
- `Mzk1G1SeparationToUFLEConsumerActual` FAIL 18:31:53 = **missing dependency olean**
  (`Mzk1G1SeparationToUFLEActual`); that file has been queued now (NO-EVENT pending).
=> R5 chain: wait for `SeparationToUFLEActual` -> `SeparationInputActual` (infra window) ->
consumer; no code fix indicated yet.


## POST-RESTART STATE 2026-11-18 18:41

- Watchdog restarted 18:41:12 (max=10, pending=50); the three previously verified DONEs
  remain DONE: `Mzk1G1MonogenicMinpolyBridgeActual` 18:30:05, `Mzk1G1F2ThetaCompositumDegreeActual`
  18:27:03, `Mzk1G1R3FourCriterionActual` 18:23:05 (latest-print axiom clean for FourCriterion;
  stale sorryAx lines in the old log are from earlier attempts).
- **New in flight: `Mzk1G1F7PrimeClassesActual`** (START 18:41:13): source has
  `f7_tame_delta_eq_ramification_sub_one`, `f7_wild_contribution_le`,
  `structure F7PrimeClassContributionData (S : Finset ℕ)`,
  `F7PrimeClassContributionData.DL_le_sum_bound` -- this is the R7 §9.1
  three-class contribution / `D(L) <= Σ log p` machinery; verify when DONE.
- Also in flight: `Mzk1G1SeparationInputActual`, `Mzk1G1SeparationToUFLEConsumerActual`,
  `Mzk1G1R3LegendrePsi2TwoActual`, `Mzk1G1F2ThetaBadTateActual`, `Mzk1URThetaKJ1BridgeActual`,
  `Mzk1ULR1FiberPrimeFActual`, `Mzk1G1F3SQInputActual`, `Mzk1G1SchemeRamBridgeActual`.

### BridgeQPaperM residual (sophie) - code handoff
- FAIL 18:28:26: `unfold` failed to unfold `qVFamNormalizedCoefficient` because after removing
  the `open QVFamNormalizedCoefficientActual` the unqualified name resolves to
  `QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient` (goal shows that name);
- recommended fix: restate the theorem with the FULLY QUALIFIED
  `QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient T b` in the STATEMENT and rewrite
  with its `qVFamNormalizedCoefficient_eq_tensor`/`_eq_order` lemmas instead of `unfold`
  (unfold of the supply version is not definitional here).


## INCIDENT 2026-11-18 18:43: SchemeRamBridge truncation (honest history + recovery)

- `Mzk1G1SchemeRamBridgeActual` FAIL 18:43:09 with `331:76 error: unexpected end of input`
  plus `simp made no progress` (312:4) and a `simp only` unused-arg linter error: the source
  had been TRUNCATED mid-proof at the 331 line (missing closing tactic/blocks).
- RECOVERY: the file was repaired by its owner at 18:45:57 (mtime), tail now ends correctly
  with `#print axioms hbridge_of_derivative_notMem`, `end namespace`, `end`; the truncation
  is no longer present in the source at audit time.
- STATUS: last watchdog verdict is still the pre-repair FAIL 18:43:09; recompile pending
  (do not cite the pre-repair FAIL as a code verdict).  If the recompile still fails, the
  remaining errors to fix are the `simp only` argument list (drop `Scheme.Hom.mem_smoothLocus`)
  and the `simp made no progress` at 312:4.

## Tail checks 2026-11-18 18:43-18:45

- **BadTate v4**: still FAIL 18:43:08 with `sorryAx` on `thetaBadTateData_Kv` (and earlier
  `thetaBadTateData_pi`, `thetaBadTateData_p_eq_qVFamTensorP`) -> the v4 fix did NOT remove
  the sorry-based data; grace must replace the `sorry`s (code, not infra).
- **F7PrimeClasses**: FAIL 18:42:30 `... of sort Type (u_1 + 1) in the application` -> CODE
  universe/sort mismatch in the `F7PrimeClassContributionData`-related application (not
  infra); the intended R7 §9.1 content (tame delta, wild contribution, DL_le_sum_bound)
  is present in source but needs the universe fix.


### 2026-11-18 18:47-18:49 v5/recovery tails (stale-verdict status)

Source mtimes are NEWER than the last verdicts (verdicts stale, recompiles queued):
- `Mzk1G1F2ThetaBadTateActual`: mtime 18:47:31, size 5089 (v5 edit after the 18:43:08
  FAIL).  The 18:43:08 verdict still shows `sorryAx` on `thetaBadTateData_Kv`/`_pi`/
  `_p_eq_qVFamTensorP` - **that is the pre-v5 state**; v5 verification pending recompile.
- `Mzk1G1SchemeRamBridgeActual`: mtime 18:48:07, size 17363 (repaired again after the
  truncation at 331:76); the 18:43:09 FAIL (unexpected end of input + simp errors) is the
  PRE-repair state; recompile pending.
- `Mzk1G1F7PrimeClassesActual`: mtime 18:48:07, size 3424 (rewritten after the 18:42:30
  universe/sort FAIL); recompile pending.
All three have been re-queued (wd_add) just now; verdicts should not be cited until the
next DONE/FAIL appears.  Incident history (SchemeRamBridge truncation) is preserved above.


## TAILS 2026-11-18 18:52-18:54 (reclassified)

- **H1** `Mzk1G1F2H1VanishingDataActual` FAIL 18:44:46: **CODE** -
  `H1VanishingData.indexFormula` depends on **`sorryAx`** (plus warning: overlapping instance
  parameters `[HasPrincipalDivisors]`/`[IsCurveOver]`).  Fix: emmy must remove the sorry in
  `indexFormula` (derive from `RiemannIndexFormula` donor or carry as an explicit field), and
  drop the redundant instance binder.
- **BadTate** FAIL 18:54:12: **CODE** - still `sorryAx` on `thetaBadTateData_Kv` and
  `thetaBadTateData_p_eq_qVFamTensorP` (v5 did not remove the sorry-based data).
- **SchemeRamBridge** FAIL 18:52:25: contains **infra** `.olean.private`
  (`Mathlib/GroupTheory/GroupAction/Period`) in the latest attempt; the `331:76 unexpected end
  of input` + `simp` errors shown in the same log are from the PRE-repair attempt (source was
  repaired at 18:48:07 and its tail is complete).  Recompile needed in a clean window; if the
  truncation line reappears, the repair was insufficient.
- **F7PrimeClasses** FAIL 18:52:11: **CODE** type mismatch -
  expected `Mzk1G1RelativeDifferentLogActual.differentExponent P = e - 1`, i.e.
  `f7_tame_delta_eq_ramification_sub_one` statement/term mismatch; note that
  `f7_wild_contribution_le` and `F7PrimeClassContributionData.DL_le_sum_bound` axiom prints
  are CLEAN (`[propext, Classical.choice, Quot.sound]`), so only the tame-delta lemma needs
  the fix.


## TAILS 2026-11-18 18:57-19:01 (detailed)

- **H1** `Mzk1G1F2H1VanishingDataActual` FAIL 18:59:30: code has **TWO `sorryAx`** declarations:
  `A3H1VanishingData.degree_neg` and `H1VanishingData.indexFormula` (plus overlapping-instance
  warning and additional infra `.olean.private` read failures in the same attempt).
  Fix (emmy): remove both sorrys (derive from Riemann-index/donor or make explicit fields).
- **BadTate** FAIL 18:58:47: still `sorryAx` on `thetaBadTateData_Kv`, `thetaBadTateData_pi`,
  `thetaBadTateData_p_eq_qVFamTensorP` - v6 did NOT remove them (code).
- **SchemeRamBridge** FAIL 18:57:06: root cause found - the source's last line was the NAMESPACE
  `end` but the file's `noncomputable section` (line 57) was NEVER CLOSED -> `331:76 unexpected
  end of input`.  FIXED: appended the missing final `end` and re-queued (START 19:01:28).
  The `simp made no progress` (312:4) and unused-simp-arg warnings may surface next; if so they
  are the remaining code items.
- **F7PrimeClasses**: verdict FAIL 18:57:06 (tame-delta type mismatch) is STALE - source mtime
  19:00:24 is newer; recompile pending.


## UPDATE 2026-11-18 19:02: `Mzk1G1F7PrimeClassesActual` DONE (R7 §9.1 three-class wiring)

- **DONE 19:02:21**; no `sorry`/`admit` in source;
- Declarations (3):
  - `f7_wild_contribution_le {p} [Fact p.Prime] {e δ} (he : 0 < e) ...`
    (wild-class normalized contribution; axiom print clean `[propext, Classical.choice, Quot.sound]`);
  - `structure F7PrimeClassContributionData (S : Finset ℕ)`;
  - `F7PrimeClassContributionData.DL_le_sum_bound {S : Finset ℕ} ...`
    (**`D(L) <= Σ log p + C` wiring**; axiom print clean).
- Note: the earlier standalone tame-delta theorem
  (`f7_tame_delta_eq_ramification_sub_one`, which had the `differentExponent P = e-1` type
  mismatch at 18:57) is NOT present in the green file - the tame clause is instead supplied
  by the donor `Mzk1G1F7TameMonogenicActual.differentExponent_eq_ramification_sub_one_of_monogenic`
  imported at the top (per the file header).  So the file has 3 declarations, not 4.
- R7 status: three-class wiring + `DL_le_sum_bound` now green; the tame statement lives in the
  donor; the remaining R7 item is the application to the actual Fermat lift `L` (same L, same
  y per route §9.1 L613).

### Environment
- Watchdog restarted with **DAG_MAX=4** (start script changed; backup kept) after the infra
  read-failure streak; expect fewer parallel heavy compiles.


## TAILS 2026-11-18 19:02-19:05 (watchdog DAG_MAX=4, PID 31772 started 03:04:52)

- **`Mzk1HTF4R6CrosswalkActual` FAIL 19:05:24 = CODE**: multiple `Application type mismatch`
  errors at 42:34, 47:24, 48:26, 54:30, 55:31 and `unsolved goals` at 48:55, 57:2, 61:2
  (the R6 crosswalk implementation file - andrew's lane).  Note: the axiom prints for
  `baseDiv_completion_eq` and `R6MetricData.sum_lambda` ARE clean tri, and a linter suggests
  omitting `[Fintype ι]` from a theorem; the failing part is the later crosswalk lemmas.
  This is exactly the R6 crosswalk (completion-to-degree/baseDiv/per-place metric) whose
  OPEN status is documented in `coord/R6-R41-CROSSWALK-DOC.md`.
- **`Mzk1G1R3LegendrePsi2TwoActual` FAIL 19:02:13 = CODE**: `psi2AtTwo_mul_cube` depends on
  **`sorryAx`** (the corrected M2 identity psi2(2P)*psi2(P)^3 = prePsi4 is sorry-based; there
  are also unused-simp-arg warnings).  This is the exact identity from the R3 acceptance doc;
  the sorry must be replaced by a real proof.
- **`Mzk1G1F2ThetaIndexTablesActual` FAIL 19:02:10 = CODE**: `76:14 Unknown constant
  `fiber_sum_split`` plus a type mismatch earlier; missing donor/import for the fiber-sum split.
- **`Mzk1G1SeparationInputActual`**: re-queued (START 19:04:53), verdict pending.
- `Mzk1G1SchemeRamBridgeActual` also START 19:04:53 (after the missing-`end` fix) - verdict
  pending.


## DONE 2026-11-18 19:08: `Mzk1ULR0BarAdapterActual` (R0.3 adapter)

- **DONE 19:08:03**; no sorry; all four axiom prints clean `[propext, Classical.choice,
  Quot.sound]`;
- Declarations:
  - **`hBar_adapter (x : L) : hBar L x = Height.logHeight₁ x / (finrank ℚ L : ℝ)`**
    (unnormalized logHeight₁ divided by [L:Q]);
  - **`D_adapter : D L = logDifferentF L`** (rfl);
  - **`D_adapter_rootDiscr : D L = Real.log (NumberField.rootDiscr L)`**;
  - **`D_adapter_absNorm : D L = Real.log ((Ideal.absNorm (differentIdeal (𝓞 ℚ) (𝓞 L)) : ℕ) : ℝ)
    / (finrank ℚ L : ℝ)`**.
- R0.3 consumers (D1 height/cond) can now use these adapters directly; paper refs in
  docstring (`IV L1206-1235`, `L2483-2488`).

## Current DONE/blockers snapshot (2026-11-18 19:09)

DONE (recent, verified): F7PrimeClasses 19:02:21 (3 decls, clean), BarAdapter 19:08:03,
KHP5Bridge 18:12:16 (fixed docstring), MonogenicMinpolyBridge 18:30:05, CompositumDegree
18:27:03, FourCriterion 18:23:05, TwoNsmulY 18:16:53, TwoNsmulPsy2 18:19:47, CPrimeFiber
18:04:00, RootNu 18:04:01, Compositum 18:04:57, TorsionCoords 18:02:32.
Blockers (code, verified): H1 two sorryAx (`A3H1VanishingData.degree_neg`,
`H1VanishingData.indexFormula`); BadTate three sorryAx (`thetaBadTateData_Kv/_pi/
_p_eq_qVFamTensorP`); LegendrePsi2Two `psi2AtTwo_mul_cube` sorryAx; ThetaIndexTables unknown
`fiber_sum_split` (76:14); R6Crosswalk type mismatches (42-61); F7LiftTower FAIL; R5
`SeparationInput` re-queued (verdict pending); `Mzk1G1SchemeRamBridgeActual` missing-`end`
fixed and re-queued (verdict pending).

### 2026-11-18 19:29 R6Crosswalk axiom probe DONE 19:29:39: 8/8 decls clean trio (completeToDegree, isHomogeneous, eval, baseDiv_completion_eq, R6SchemeBaseDivData, R6MetricData, lambda, sum_lambda).

## VERIFIED 2026-11-18 19:32 (exact names/axioms)

- `Mzk1G1F2ThetaBadTateActual` **DONE 19:32:22**; `#print axioms` list (4):
  - `ksUniformizer_ne_zero` → `[propext, Classical.choice, Quot.sound]`;
  - `thetaBadTateData_Kv` → `[propext, Classical.choice, Quot.sound]`;
  - `thetaBadTateData_pi` → `[propext, Classical.choice, Quot.sound]`;
  - `thetaBadTateData_p_eq_qVFamTensorP` → `[propext, Classical.choice, Quot.sound]`;
  (structures/defs also present: `ThetaKummerRootData`, `ThetaBadTateData`, `ksUniformizer`,
  `thetaBadTateData`; only linter warnings for unused `[Fintype (Bad ...)]` sections vars.)
  **No `sorryAx` remains** (the previous three sorryAx decls are now clean).
- `Mzk1URBadPlaceActualMapActual` **FAIL 19:32:03**: `Mzk1URBadPlaceActualMapActual.lean:92:6:
  error(lean.synthInstanceFailed): failed to synthesize instance of type class
  MeasurableSpace (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)`
  (code: missing/needs-provided MeasurableSpace instance for the arithmetic tensor tuple block).


## VERIFIED 2026-11-18 19:37-19:38 (R5 separation, exact names/axioms + duplicates)

- `Mzk1G1SeparationInputActual` **DONE 19:30:30**: `structure SeparationInputIngredients (p) [Fact p.Prime] (d) : Prop`,
  **`separationInput_of_differentBound (d)`** → `[propext, Classical.choice, Quot.sound]`.
- `Mzk1G1SeparationInputDoneActual` **DONE 19:38:47**: SAME declarations (`SeparationInputIngredients`,
  `separationInput_of_differentBound` → tri) -> **DUPLICATE of SeparationInputActual**.
- `Mzk1G1SeparationToUFLEConsumerActual` **DONE 19:37:35**: `universalLocalFieldExists_of_separationInput' (d B)`,
  `universalLocalFieldExists_of_conservative (d)`; printed `_of_separationInput'` → tri.
- `Mzk1G1SeparationToUFLEConsumerDoneActual` **DONE 19:37:35**: SAME two declarations, both printed
  `[propext, Classical.choice, Quot.sound]` -> **DUPLICATE of SeparationToUFLEConsumerActual**.
- `Mzk1G1SeparationInputFinalActual` **FAIL 19:29:53** (third variant; log has unused-`hn` warning and
  failed olean reads) -> redundant/stale third file.

Duplicate/redundant flags: {SeparationInputActual, SeparationInputDoneActual} identical;
{SeparationToUFLEConsumerActual, SeparationToUFLEConsumerDoneActual} identical;
SeparationInputFinalActual redundant (failing).  Canonical choice recommended: keep
SeparationInputActual + SeparationToUFLEConsumerActual (earlier, both green).


## VERIFIED 2026-11-18 19:40-19:45 (new DONE, exact names/axioms)

- `Mzk1ULR1MpaperBWeightActual` **DONE 19:40:56**: `noncomputable def cPFullFiber (b)`,
  **`MpaperB_eq_neg_qPilotMass (b)`** -> `[propext, Classical.choice, Quot.sound]`;
  (fiber-prime lemma `natAbs(underIntGen P) = qVFamTensorP b` used).
- `Mzk1HTF4R6CrosswalkActual` **re-DONE 19:43:58** (previous DONE 19:20:03); the axiom
  probe `Mzk1HTF4R6CrosswalkAxiomProbeActual` (DONE 19:29:39) printed 8/8 clean
  `[propext, Classical.choice, Quot.sound]`.
- `Mzk1G1SeparationToUFLEConsumerActual` **re-DONE 19:44:07**:
  `universalLocalFieldExists_of_separationInput' (d B)`, `universalLocalFieldExists_of_conservative (d)`;
  last print clean tri.
- `Mzk1G1SchemeRamBridgeActual` **DONE 19:44:43** (obligation file; docstring NOTE
  `(obligation: scheme_ram_bridge)`; source has NO `sorry`/`admit` - only the docstring says
  "No sorry, no admit, no new axioms"): decls include `chartTToPoly`, `polyToChartT`, the
  four inverse/comp lemmas, `chartTPolyAlgEquiv`, `chartTPolyRingEquiv`, `chartTToPoly_chartMap`,
  `mem_smoothLocus_specMap_comp`, `smoothLocus_congr`, `mem_smoothLocus_specMap_algebraMap_of_smooth_away`,
  `smooth_specMap_algebraMap_away`, `locallyOfFinitePresentation_specMap_chartMap`,
  `hbridge_of_derivative_notMem`, `smoothCriterion_of_chartT_of_ram`; latest prints clean tri
  (log's `sorryAx` at 146 and rewrite/olean errors are STALE earlier attempts).
- `Mzk1URBadPlaceActualMapActual` **DONE 19:44:46**: `noncomputable def badPlaceCoeff`,
  **`badPlaceCoeff_norm`**, `noncomputable def badPlaceQRegion`, **`badPlaceQRegion_nu`**;
  latest print clean tri (proved content only; the sigma/MeasurableSpace donor note from
  19:32 is superseded by this green file).
- `Mzk1ULR0COldActual` (david) **FAIL 19:43:58 (no log file)** - no verdict yet; source contains
  `neg_log_norm_eq_order_div_e`, `cOld_eq_ef_mul_cP`, `cOld_eq_cP_iff_ef_one`; no axiom output
  available.


## CORRECTION 2026-11-18 19:48 (re-audit of SchemeRamBridge / BadPlaceActualMap; supersedes my 19:40-19:45 bullet)

### SchemeRamBridge `Mzk1G1SchemeRamBridgeActual` DONE 19:44:43
- CURRENT file decls (grep theorem/def lines) are exactly the DIRECTION-B SUBSET:
  `chartTToPoly`, `polyToChartT`, `chartTToPoly_X`, `polyToChartT_X`,
  `chartTToPoly_comp_polyToChartT`, `polyToChartT_comp_chartTToPoly`, `chartTPolyAlgEquiv`,
  `chartTPolyRingEquiv`, `chartTToPoly_hElt`, `chartTToPoly_hDerivElt`, `chartTToPoly_chartMap`,
  `chartTToPoly_algebraMap`, `chartTPolyRingEquiv_comp_chartMap`, `mem_smoothLocus_specMap_comp`,
  `smoothLocus_congr`, `mem_smoothLocus_specMap_algebraMap_of_smooth_away`, `smooth_away_hDerivElt`,
  `smooth_specMap_algebraMap_away`, `locallyOfFinitePresentation_specMap_chartMap`,
  `mem_smoothLocus_specMap_chartMap_of_deriv_notMem`, `mem_smoothLocus_specMap_evalAt_of_deriv_notMem`,
  `smoothAt_of_derivative_notMem_chartInf` (last declaration, line 335).
- **`hbridge_of_derivative_notMem` and `smoothCriterion_of_chartT_of_ram` are NOT declared in the
  current file**: they appear only in the docstring bullets (lines ~42/45) and in the closing
  NOTE comment (`(obligation: scheme_ram_bridge)`, lines ~351-356), which states Direction B of
  the SmoothCriterion and that the downstream declarations were LOST in a truncation incident
  and cannot be reconstructed without guessing (PrimeSpectrum vs Spec point-type mix).
- So the DONE status means: direction-B subset proved + a REGISTERED OBLIGATION; it is NOT a
  closure of hbridge/smoothCriterion.  The old log prints naming hbridge/smoothCriterion
  (lines 146/150) are from the PRE-truncation version - stale, not current.
- Current-file axiom probe (`Mzk1G1SchemeRamBridgeAxiomProbeActual`) queued (NO-EVENT so far);
  the 6 `#print axioms` targets in the source are `mem_smoothLocus_specMap_comp`, `smoothLocus_congr`,
  `mem_smoothLocus_specMap_algebraMap_of_smooth_away`, `mem_smoothLocus_specMap_chartMap_of_deriv_notMem`,
  `mem_smoothLocus_specMap_evalAt_of_deriv_notMem`, `smoothAt_of_derivative_notMem_chartInf`.

### BadPlaceActualMap `Mzk1URBadPlaceActualMapActual` DONE 19:44:46
- EXACT declarations (4): `noncomputable def badPlaceCoeff`, **`badPlaceCoeff_norm`**,
  `noncomputable def badPlaceQRegion`, **`badPlaceQRegion_nu`**;
  printed axioms: `badPlaceCoeff_norm` and `badPlaceQRegion_nu` -> `[propext, Classical.choice,
  Quot.sound]` clean.
- The file STILL CONTAINS the MISSING DONOR comment (lines 85-94): named OPEN
  `badPlaceActualMap_remaining` = the actual source-action map
  `sigma : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple -> ksBlock T b`
  and the Haar pushforward comparison `Measure.map sigma addHaar = (local degree) * addHaar`,
  needed for `nu(sigma '' J_b) = nu(J_b)`; NO donor exists.  There is NO `sigma`, NO `MapsTo`
  in the file.
- => DONE proves only the 4 items above; `badPlaceActualMap_remaining` remains OPEN.  My earlier
  statement that the 19:32 sigma/MeasurableSpace note was superseded was WRONG.


## VERDICTS 2026-11-18 19:55-19:56 (exact)

- `Mzk1ULR0D1WiringActual` - **START 19:55:47** (no verdict yet); decls in source:
  `discOver_eq_D : discOver K = D K`, `hBar_wiring (x : K)`, `truncConductor_def_wiring (lam : K)`.
- `Mzk1G1ProbeKQpActual` - **FAIL 19:56:01**; `logShellRamificationExponent_le_finrank_KQp`
  depends on **`sorryAx`** (`[propext, sorryAx, Classical.choice, Quot.sound]`); decls:
  `qpToFrac`, `fracAlgEquiv`, `finrank_frac_eq`, `logShellRamificationExponent_le_finrank_KQp`.
- `Mzk1G1R3Psi2TwoGeneralActual` - **FAIL 19:55:15**:
  `Mzk1G1R3Psi2TwoGeneralActual.lean:21:0: error: (deterministic) timeout at `whnf`, maximum
  number of heartbeats (200000) has been reached` (source mtime 19:52:10 < FAIL, so current);
  target theorem `psi2AtTwo_mul_cube_general {x y} (hEq : y²+a₁xy+a₃y = x³+a₂x²+a₄x+a₆)
  (hd : 2y+a₁x+a₃ ≠ 0) : psi2AtTwo W x y * (2y+a₁x+a₃)³ = (W.preΨ 4).eval x`.


## VERDICT 2026-11-18 19:59: BadTate re-DONE (axioms)

- `Mzk1G1F2ThetaBadTateActual` **re-DONE 19:59:09**; all four printed declarations are clean
  `[propext, Classical.choice, Quot.sound]`:
  `ksUniformizer_ne_zero`, `thetaBadTateData_Kv`, `thetaBadTateData_pi`,
  `thetaBadTateData_p_eq_qVFamTensorP` (no sorryAx); only linter warnings for unused
  `[Fintype (Bad ...)]` section variables.
- Canonical-lift audit: no kurt-provided canonical-lift file exists in the tree yet
  (`Get-ChildItem *CanonicalLift*` finds only the old `S2114CanonicalLiftTwoCellActual`), so
  the feasibility audit starts when the file lands.


## TAILS 2026-11-18 20:01 (exact)

- `Mzk1URCanonicalLiftActual` **START 20:01:13 (no verdict)**; no axiom output yet.
  Declarations (source): `nativeBadLiftCanonical (b)`, `nativeBadLiftCanonical_comap (b)`,
  `nativeBadLiftCanonical_comap_Fmod (b)`, `canonicalLift_alignment (b)`,
  `canonicalQFamTensorPlace (b)`, `canonicalQFamTensorPlace_eq_contraction (b)`.
  Source comments state the defining property is `:= rfl` (`nativeBadLiftCanonical_comap` line 33),
  `canonicalLift_alignment` line 42-44: "ASSESSMENT: with the canonical lift the alignment
  `NativeBadLiftAlignment` is rfl" with statement
  `nativeBaseContractionFPlace T b = nativeBadLiftCanonical (T := T) b := rfl`, and
  `canonicalQFamTensorPlace_eq_contraction := rfl`.  There is NO identifier named `lift_comap`
  in the file.  All of this is UNVERIFIED/kernel-pending (file still compiling).
- `Mzk1URCompletionMapQpActual` **START 20:01:13 (no verdict)**.
- `Mzk1HTF4R6HeightBoundActual` **START 20:01:13 (no verdict)**.

### 2026-11-18 20:03 FiveKernel DONE 20:03:06 (five_smul_eq_four_smul_add / five_mem_mulKernel_iff / negY_coords_mem all clean trio; mulKernelCoords/mem_mulKernelCoords_iff defs). ProbeKQp DONE 20:03:08 (KQpRamificationBound; logShellRamificationExponent_le_finrank_KQp clean trio, sorryAx removed).

## VERDICTS 2026-11-18 20:13-20:16 (exact names/axioms)

- `Mzk1ULR0D1WiringActual` **DONE 20:16:07**: `discOver_eq_D : discOver K = D K`,
  `hBar_wiring (x : K)`, `truncConductor_def_wiring (lam : K)`; last print clean tri.
- `Mzk1G1SchemeRamBridgeAxiomProbeActual` **DONE 20:16:29**: 6/6 prints are
  `[propext, Classical.choice, Quot.sound]`: `mem_smoothLocus_specMap_comp`, `smoothLocus_congr`,
  `mem_smoothLocus_specMap_algebraMap_of_smooth_away`,
  `mem_smoothLocus_specMap_chartMap_of_deriv_notMem`,
  `mem_smoothLocus_specMap_evalAt_of_deriv_notMem`, `smoothAt_of_derivative_notMem_chartInf`.
- `Mzk1G1BaseDifferentPrereqActual` **DONE 20:13:32**: `structure BaseDifferentTop : Prop`,
  `localDifferentPaperOrder_rat_eq_zero_of_base (H) : ...`; clean tri.
- `Mzk1G1BaseDifferentTopInputActual` **DONE 20:13:32**: SAME declarations
  (`BaseDifferentTop`, `localDifferentPaperOrder_rat_eq_zero_of_base`) -> **DUPLICATE of
  BaseDifferentPrereqActual**.
- `Mzk1HTF4R6HeightBoundActual` **DONE 20:14:45**: `structure R6IV3172HeightData`,
  `R6IV3172HeightData.hE_le (D) : ...` (IV:3172 erratum form).
- `Mzk1G1F2ThetaTensorQVFamAlignmentActual` **DONE 20:14:52**: `thetaTensorQVFamAlignmentOfActual`,
  `thetaTensorQVFamAlignmentObstruction_actual`; last print clean tri (non-vacuous on the
  Bad-indexed packet per 20:04 audit).
- `Mzk1G1F2ThetaIndexTablesActual` **DONE 20:16:19**: `structure ThetaQIndexTable`,
  `structure ThetaFiberLiftTable (b)`, `fiber_sum_split (b)`, `currentBad_Q_split_and_nonneg`,
  `nonBadQ (Tab)`, `nonBadQ_card_add_badQ (Tab)`, `nonBadQ_card_le (Tab)`, `fiberTableOfBad (b)`,
  `fiberTableOfBad_used (b)`; last print clean tri.


## VERDICTS 2026-11-18 20:27-20:30 (exact)

- `Mzk1URRootExchangeSquareActual` **DONE 20:28:04**: `rootMass_eq_half_blockMass` -> tri;
  `thetaMass_eq_gauss_mul_alphaMass (j)` -> tri; also `thetaSum_eq_gaussSum_mul_alphaMass`;
  all printed blocks `[propext, Classical.choice, Quot.sound]`.
- `Mzk1BoxActualR2Actual` **DONE 20:27:15**: `noncomputable def W` and
  `actual_weightedAverage_le_of_distinguished` -> `[propext, Classical.choice, Quot.sound]`.
- `Mzk1ULR1FiberPrimeFActual` **DONE 20:30:00**: `qVFamTensorPlace_under (b)` -> tri;
  `fiber_prime_consistency_F (b)` -> tri.
- `Mzk1URBadPlaceActualMapActual` **FAIL 20:30:01 = CODE REGRESSION** (log
  `dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1URBadPlaceActualMapActual.lean.log`):
  - `Mzk1URBadPlaceActualMapActual.lean:104:56: error: Function expected at`
  - `:105:6: error: Function expected at`
  - `:115:32: error: Invalid argument name `T` for function`
  - `:116:27: error: Function expected at`
  root cause from log: `nativeBaseContractionFPlace` is UNKNOWN (missing import/open), so it is
  treated as an implicit variable; earlier printed axioms (`badPlaceCoeff_norm`,
  `badPlaceQRegion_nu`) are from the prior green version and remain tri.


## VERDICTS 2026-11-18 20:28-20:36 (exact; DONE re-check + regressions)

- DONE (re-confirmed): `Mzk1ULR1FiberPrimeFActual` 20:30:00 (`qVFamTensorPlace_under`,
  `fiber_prime_consistency_F` tri); `Mzk1URRootExchangeSquareActual` 20:28:04
  (`rootMass_eq_half_blockMass`, `thetaMass_eq_gauss_mul_alphaMass`, `thetaSum_eq_gaussSum_mul_alphaMass` tri).
- `Mzk1BoxActualR2Actual` **REGRESSED: FAIL 20:34:53 = CODE** (was DONE 20:27:15):
  `Mzk1BoxActualR2Actual.lean:43:1: error: unexpected token '*'; expected term`; current
  attempt's `#print axioms actual_weightedAverage_le_of_distinguished` shows `sorryAx`.
- `Mzk1URBadPlaceActualMapActual` **FAIL 20:30:01 = CODE**: `:104:56`/`:105:6` Function expected,
  `:115:32` Invalid argument name `T`, `:116:27` Function expected; root: unknown
  `nativeBaseContractionFPlace` (missing import/open).
- `Mzk1G1R4ProtectedActual` **FAIL 20:35:39 = INFRA (OOM)**: log ends with
  `libc++abi: terminating due to uncaught exception of type std::bad_alloc: std::bad_alloc`.
- `Mzk1ULR0FiberCrosswalkActual` **FAIL 20:35:42 = CODE**: unsolved goal after `hsum'`
  (goal display: `inertiaDeg * finrank Fmod F * vsel * dModF = inertiaDeg * vsel * finrank ℚ F`);
  current `#print axioms cPFullFiber_eq_thetaLamWeight_mul_cP` shows `sorryAx`.

### 2026-11-18 20:41 donors S2746/S2796/S2797: all NO-EVENT (no verdict). Statements recorded (c3NormalizedTensorHaar/c3TensorLattice_self_measure/tensorLattice_subset_C3RegionAll; coordinateLattice_subset_regionAll; S2796_absNorm_supportIdeal_le_radSq; S2797FieldOfModuli/S2797ClauseA; S2797 tensorLattice_subset_regionAll).

## VERDICTS 2026-11-18 20:44 (exact names/axioms)

- `Mzk1BoxActualR2Actual` **re-DONE 20:44:05** (previous FAIL 20:34:53 code, fixed):
  `noncomputable def W {E} {j} (lam : E → ℝ) (t : Fin (j+1) → E) : ℝ`;
  `actual_weightedAverage_le_of_distinguished` -> `[propext, Classical.choice, Quot.sound]`.
- `Mzk1G1F2ThetaCoeffRowActual` **DONE 20:44:20**: declarations
  `thetaCoeffRow (b)`, `thetaCoeffRow_apply (b)`, `thetaCoeffRow_eq_alignment (b)`,
  `structure ThetaQVFamRow (l) (T)`, `thetaQVFamRowOfBad (b)`, `thetaQVFamRowOfBad_places (b)`,
  `thetaQVFamRowOfBad_coeff (b)`; printed blocks: `thetaCoeffRow_eq_alignment` -> tri;
  `thetaQVFamRowOfBad_places` -> tri; `thetaQVFamRowOfBad_coeff` -> tri.


## VERDICTS 2026-11-18 20:46-20:50 (exact names/axioms)

- `Mzk1URBadPlaceActualMapActual` **re-DONE 20:46:17** (previous 20:30:01 code fail fixed):
  `noncomputable def badPlaceCoeff`, `badPlaceCoeff_norm`, `noncomputable def badPlaceQRegion`,
  `badPlaceQRegion_nu` -> `[propext, Classical.choice, Quot.sound]`.
- `Mzk1BoxR2PerRowActual` **DONE 20:49:28**: `perRow_eq_collectionBound` ->
  `[propext, Classical.choice, Quot.sound]`.
- `Mzk1G1R1IFractionalLatticeNormActual` **DONE 20:49:32**:
  `padicFractionalLattice_log_norm_le (a : ℝ) (x : K) (hx0 : x ≠ 0)` -> tri.
- `Mzk1G1R1IAlphaMassConnectorActual` **DONE 20:50:17**:
  `urRootAlpha_mass_eq_badPlaceQRegion_nu`, `urRootAlpha_pow_eq` -> tri (latest block).
- `Mzk1G1R1IAlphaMassConnectorDoneActual` **START 20:49:28 (no verdict)**: duplicate-shaped
  file with the same two declarations (`urRootAlpha_mass_eq_badPlaceQRegion_nu`,
  `urRootAlpha_pow_eq`) - redundant until compiled; canonical = ConnectorActual.


## VERDICTS 2026-11-18 21:0x-21:5x (new batch / hW / localCompletionDegree)

- `Mzk1PaperBlockTargetActual` **DONE 21:01:06**: `lambdaORegion_zero_mem_candidate`,
  `leastLambdaOHull_subset_lambdaORegion_zero`, `lambdaORegion_zero_measure_lt_top`,
  `paperHull_measure_lt_top`, **`qPilotPaperRegionLog_le_paperHullLog_unconditional`**, `rows`;
  no `#print axioms` in log (probe `_ProbePaperBlockTargetAxiomsActual` queued, NO-EVENT).
- `Mzk1BoxR2RouteCheckActual` **DONE 21:06:33**: single `def PaperThetaReadout_le_perBThetaHullLog
  (paperReadT perBThetaHull : ℝ) : Prop := paperReadT ≤ perBThetaHull` — i.e. the target
  inequality IS the named Prop.  Header verdict (quoted): prior chain gives the F-side root
  hull inequality only; the paper R2/IV:1585 bound is on the paper Θ source-box readout
  `read(T)` (resp. first-row ceil), NOT on `ksThetaHull`/`perBThetaHullLog`; present tree has
  `A508ThetaPilotObjectActual.thetaPilotLog p N = -N log p` but **no declaration** equating it
  (or a source-box read(T)) with `collectionChoiceBound`/`perBThetaHullLog` ⇒ prior chain does
  NOT by itself give the paper Θ R2 upper bound; missing bridge named above.
- hW: `Mzk1HWConsumerActual.hwConsumerRows` / `Mzk1HWConstantActual.hwConstantRows` are
  `List (String × String × String)` ROW TABLES (names/status), not mathematical inequality
  claims; no hW theorem asserting the bound was found in those files.
- `localCompletionDegree` has TWO definitions with the SAME name:
  `Mzk1P7ThetaDegActual:30 def localCompletionDegree (place : FinitePlaceAtPrime K p) : Nat :=
  `Module.finrank ℚ_[p] (CommonPrimeCompletion place)` (ABSOLUTE [K_v:Q_p]); vs
  `ProcessionNormalizationWeightsActual:49 noncomputable def localCompletionDegree {l}
  (T : InitialThetaArithmeticData l) (w : FiniteFieldPlace T.K) : Nat := …` (RELATIVE
  [K_w:(Fmod)_v]).  Same name, different meanings - naming collision / consumption hazard.
- My `_ProbeR1R2HandoffAxiomsActual` **FAIL 20:31:17 = DEPENDENCY/INFRA**: log
  `object file '...Mzk1URThetaHullInclusionActual.olean' does not exist` (module not compiled).

### 2026-11-18 22:10: S716 NO-EVENT (queued, watchdog 77-pending, no run); RouteCheck not yet recompiled; Mzk1URPaperThetaR1FinalActual FAIL code (:31:19 Unknown Mzk1ULR1CPrimeFiberActual.cPFullFiber, :33:16 Unknown .Qb, :30/:32/:36 Invalid argument name l, :44:50 Unknown thetaLamWeight_pos; sorryAx in print). PaperBlockTarget discarded (S800 least hull log 0).

## RULING 2026-11-18 22:1x: R2 needs INEQUALITIES only (Lead)

DO NOT chase equalities `paperBound = collectionChoiceBound` or `λ = slot`/`exc = ...`.
R2 only needs: `V ≤ paperBound` (DONE) + `λ ≥ slot`, `dsum ≤ Σd`, `exc ≤ 4(j+1)·iota`,
`logp ≥ 0` => `V ≤ collectionChoiceBound`.  The equality StepVBridge/`hparam` is OBSOLETE;
ignore it.  Focus on the actual `et, d, oq, hD` and the `λ ≥` identification.

### Exact donors (verified names/sites)
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:814`
  `theorem arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound [DecidableEq ι]`
  -- the `V ≤ paperBound` donor (DONE olean in core).
- `LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean:125`
  `noncomputable def collectionChoiceBound (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ)
  (et : Fin (j+1) → E) (idag : Fin (j+1)) : ℝ :=
  `(-((j:ℝ)^2/(2*l)*oq (et idag)) + Σ i, d (et i) + 1) * logp + 4*((j:ℝ)+1)*iotaL`.
- `LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean`
  `theorem exceptionalSum_le_r4 (I Istar) (hsub : Istar ⊆ I) (e) (p el) (hel : 1 ≤ el)
  (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4*Real.log el) :
  Σ i ∈ Istar, (3 + Real.log (e i)) ≤ 4*(I.card:ℝ)*(if p ≤ el then Real.log el else 0)`
  -- the `exc ≤ 4·|I|·ι·log el` (hence `≤ 4(j+1)iota`) donor.
- `LeanFormal/IUT/IUTIV/Estimates/StepVDistinguishedSlotAverage.lean:87`
  `theorem weightedAverage_le_of_distinguishedBound [Nonempty E] (lam) (weights_pos)
  (l logp iotaL) (l_ne_zero) (j) (d oq) (slot) (V)
  (bound : ∀ et, V et ≤ collectionChoiceBound l logp iotaL j d oq et slot) :
  weighted average ≤ collectionBound l (weightedAvg d) (weightedAvg oq) logp iotaL j`
  -- consumes exactly the `V ≤ collectionChoiceBound` inequality (no equality needed).

### Current verdicts
- `Mzk1BoxR2StepVBridgeActual` **DONE 22:09:23** (obsolete equality `hparam`; IGNORE per ruling).
- `Mzk1BoxR2IntegrationActual` **DONE 20:52:49** (inequality-integrated consumer; takes
  `bound : ∀ t, V t ≤ collectionChoiceBound l logp iotaL j d oq t slot`).
- `Mzk1BoxStepVAverageActual` **DONE 2026-11-14 01:35:55**.
- `Mzk1BoxActualR2Actual` **re-DONE 20:44:05** (`W = ∏ λ`, `actual_weightedAverage_le_of_distinguished`).
- `Mzk1BoxR2PaperThetaRowCompareActual` **FAIL 22:09:30 = CODE**:
  `:36:4 error: Function expected at`;
  `:38:9 error: Tactic `unfold` failed: Local variable `collectionChoiceBound` has no definition`;
  `:48:50 error: Function expected at`; `:48:103 error: unsolved goals`.
  (its earlier `sorryAx` prints are stale; current source has no `sorry`.)


## FIX 2026-11-18 22:15: R2 inequality bridge de-hypothesized (no equalities)

- `Mzk1BoxR2InequalityBridgeActual` (source edited, queued; **NO-EVENT**, backlog):
  REMOVED the two non-genuine equality hypotheses:
  - `hpaper : (-lam + dsum + 1)·logp + exc = (-lam + dsum + 1)·logp + exc` (trivial);
  - `hchoice : collectionChoiceBound … = (-(j²/(2l))·oq(et idag) + Σ d(et i) + 1)·logp + 4(j+1)iotaL`
    (definitional; replaced by `unfold …collectionChoiceBound` in both proofs).
- Remaining hypotheses in the file are exactly the genuine inequality inputs per ruling:
  `hslot : (j²/(2l))·oq(et idag) ≤ lam` (the lambda >= identification),
  `hd : dsum ≤ Σ_i d(et i)`, `hexc : exc ≤ 4(j+1)·iotaL`, `hlogp : 0 ≤ logp`
  (the last one to be replaced by a proved `log p > 0` lemma at the instantiation site, per
  ruling; the abstract file keeps it as the numeric input).
- Theorems (post-edit): `paperBound_le_collectionChoiceBound` and
  `packetHull_le_collectionChoiceBound`, both `#print axioms` present; verdict pending
  (target queued, NO-EVENT).

### 2026-11-18 22:27-22:35: R1Final re-DONE 22:27:20 (neg_Mpaper_le_paperThetaSum trio; probe 22:30:17 confirms). RowV DONE 22:34:48 (rowV_le_collectionChoiceBound trio). RouteCheck DONE 22:35:22 (paperThetaReadout_le_perBThetaHullLog_instance trio; set_option placement fixed).
### 2026-11-18 22:41 R1/R2 audit: JbRootMassRoute DONE 22:38:33 (rootLatticeJ, rootLatticeJ_subset_rootNormHull trio; probe 22:41:23 confirms). RootHullAssembly NO-EVENT (rootHull_assembly). RowPacketWiring FAIL code (:66:2 Unknown identifier refine). RouteCheck DONE 22:35:22.
### 2026-11-18 22:47: Jb re-DONE 22:43:17 (rootLatticeJ, rootLatticeJ_subset_rootNormHull trio). Assembly no valid verdict (infra: missing Example36 olean + mathlib .olean.private Clique/DropRight). R2ActualInstantiation FAIL code (:67:17 Unknown identifier collectionChoiceBound, missing import/open StepVProcessionAverage).
### 2026-11-18 22:51: Jb DONE 22:43:17 (rootLatticeJ line 44, rootLatticeJ_subset_rootNormHull line 50 trio; 2 decls). RootHullAssembly DONE 22:50:53 (rootHull_assembly trio). R2ActualInstantiation FAIL code (:83:4 Application type mismatch: d : ι→ℝ expected ℝ at paperBound_le_collectionChoiceBound call). PaperThetaLeH FAIL code (:35:53 isDefEq timeout; :45:14 Unknown paperThetaWeighted_le).
### 2026-11-18 22:55: ProbeRootHullAssembly DONE 22:54:28 (rootHull_assembly trio). PaperThetaLeH DONE 22:55:34 (paperThetaReadoutB; paperThetaWeighted_le trio). R2ActualInstantiation FAIL code (:27:5 unknown namespace StepVProcessionAverage; :68:17 Unknown collectionChoiceBound; :83:4 app type mismatch). RowPacketWiring FAIL no-log stale (last content error :66:2 Unknown refine).
### 2026-11-18 23:0x audit: R1.1 closed (RootHullAssembly 22:50:53 / R1Final 22:27:20 / Jb 22:43:17, all trio; probes 22:54:28 and 22:30:17 confirm). R2: ActualInstantiation DONE 22:58:40 (packetHull_le_collectionChoiceBound trio); PaperThetaLeH DONE 23:01:51 (paperThetaWeighted_le trio); RowV DONE 22:34:48 (trio); RouteCheck DONE 22:35:22 (readout inhabitant trio); RowPacketWiring FAIL 23:03:27 NO LOG (earlier :66:2 Unknown refine).
### 2026-11-18 23:06 R2: LeHAssembly NO-EVENT (paperThetaWeighted_le_H). RowPacketWiring FAIL code (unsolved goal ... ≤ collectionChoiceBound ... at (D t); sorryAx in print). PaperThetaLeH FAIL 23:06:05 infra OOM (bad_alloc); previous DONE 23:01:51 trio stands. ActualInstantiation DONE 22:58:40 trio. ProbeR2Axioms NO-EVENT.
### 2026-11-18 23:12 R2 audit: rowPackets_weightedAverage_le_H V = vol(packetHull (D t)) on generic ArithmeticTensorTupleBlock; paperThetaReadoutB = vol(rootNormHull) on qVFamTensorBlock. NOT defeq; missing identification explicitly named (LeHAssembly header: weighted row-V average vs sum_b thetaLamWeight*paperThetaReadoutB = RouteCheck gap). Verdicts: RowPacketWiring FAIL 23:06:07 no-log (source 23:10:25 newer); LeHAssembly NO-EVENT (source 23:10:19); LeH FAIL 23:06:05 infra OOM (source 23:02:32 > DONE 23:01:51).
### 2026-11-18 23:25 R2 final: Instantiation DONE 22:58:40 (packetHull_le_collectionChoiceBound trio, mtime 22:56:10). LeH DONE 23:19:16 (paperThetaReadoutB tri; paperThetaWeighted_le trio; mtime 23:13:23). RowPacketWiring FAIL 23:18:08 code (:72:21 app mismatch Real.log_pos hp2 vs -localNormOrder < -(j^2/2l*oq); :73:28 hd t expected exceptional bound; :73:8 linarith failed), source 23:25:51 newer => stale. LeHAssembly NO-EVENT; ProbeR2Axioms NO-EVENT.
### 2026-11-18 23:30: RowPacketWiring DONE 23:28:07 (rowPackets_weightedAverage_le_H trio). Instantiation DONE 22:58:40. LeH DONE 23:19:16 (paperThetaReadoutB/paperThetaWeighted_le trio). hread statement: Mzk1BoxR2PaperThetaLeHFinalActual.lean:48-54 paperTheta_le_H_of_rowAverage with hread : sum w*paperThetaReadoutB <= rowAvg (inequality), hrow : rowAvg <= H; NO-EVENT. LeHAssembly NO-EVENT; ProbeR2Axioms NO-EVENT.
### 2026-11-18 23:35 exact first errors: LeHFinal :42:53 Function expected at perBThetaHullLog (missing import); LeHAssembly :48:53 same; LocalStepV :27:39 Function expected at rootNormedExtension, :28:3 Unknown identifier Integers (missing imports).
### 2026-11-18: R2PerRowBoxActual DONE (direct compile exit=0): perRowBox (B_j(t,s)=(-lam+dsum+1)logp+exc); perRowBox_le_collectionChoiceBound (hslot/hd/hexc/hlogp) trio; exceptional_bound_of_r4 (from exceptionalSum_le_r4 donor) trio; perRowBox_le_collectionChoiceBound_of_r4 trio.
### 2026-11-18 00:0x procession audit: ThetaProcession exit=1 (:73:9 isDefEq timeout 2M; gap stepV_hullVolume_le_processionAvg :85). PacketAverage exit=0 (reusable c3ThetaProcession*/actualThetaPacketAverage_eq_*; gap PaperProcessionEqC3ThetaProcession :147). PacketInstance exit=1 infra (.olean.private MeasureSpaceDef :14); source gaps: urActualB :57 fixed, urPacketP :62 fixed b, urPacketSlot :65 (), urPacketTuple :68 fun _=>(), urPhi_actual :102 fixed b - no real (b,j,slot) index/row H_bj/V_bj.
### 2026-11-19 00:2x FULL-REPO SEARCH F-side hperB/containment/correction: see coord/R1-P5 addendum; candidates FsideHperBActual:50/:111/:72/:90; Mzk1URThetaHullNonzeroActual urActualLocalHullRegion_eq_holomorphic; Mzk1URThetaTransportActual:83/:90/:142/:151; FsideVolumeAlignmentActual:29/:37/:47; FsideGeneratorTransportActual:33-57; Mzk1URThetaHperBReductionActual:47/:68/:80; Mzk1LpDifferentBoundActual:31/:46/:68; core localDifferentPaperOrder def :701 + bound :138. Gaps: per-row containment input; Delta_b vs localDifferentPaperOrder identification absent. Compile errors: FsideGeneratorTransport :52:6 Fintype Bad / :62:11 Integers; FsideVolumeAlignment :30:16 sourceRootQUnit.
