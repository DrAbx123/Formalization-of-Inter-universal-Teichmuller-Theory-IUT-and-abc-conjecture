# R6 paper lines + explicit-field inventory (for andrew)

Status: guidance doc (sophie, 2026-11-18). No Lean claimed. The R6.1 statement is already
in `tmp/sheaf/xif/paper/Mzk1HTF4R6Actual.lean`; this doc lists (a) the paper anchors we
can currently quote for (R6.1)-(R6.3), (b) the exact explicit fields still carried there.

## 1. R6.1: local Weil function normalization / h_E <= m h_{O(1)}

- Current Lean (`Mzk1HTF4R6Actual.R6LocalWeilData`, `hE_le_m`, `hE_le_kappa`):
  `hE = m·hO1 − hP` (`hE_eq`) with `hP = Height.logHeight x ≥ 0` (`hP_nonneg`), hence
  `hE <= m·hO1`; the kappa form uses `hnorm : m·hO1 = (m/(n−3))·hOmega`, giving
  `hE <= (m/(n−3))·hOmega`.
- Paper anchors available NOW (quoted):
  * IV L2440-2444: `log(q∀(−))` <= `Hunif·ε^{−3}_d·d^{4+εd} + HK` (D1-style height
    comparison with the uniform constant);
  * IV L2445-2476: `E_F` over `F`, `Fmod ⊆ Ftpd = Fmod(E_Fmod[2]) ⊆ F`,
    `F = Ftpd(√−1, E_Ftpd[3·5])`, `x_E ∈ K_V`;
  * IV L2477-2495: (C1) `(log(q∀))^{1/2} <= l <= 10δ(log(q∀))^{1/2}log(2δ log(q∀))`;
    (C2) `(1/6)log(q) <= (1/6)log(q∤2) <= (1/6)log(q∀) <= (1+ε_E)(log-diff_X + log-cond_D) + C_K`;
    and the dictionary `log-diff_X = log(d_Ftpd)`, `log(f_Ftpd) <= log-cond_D <= log(f_Ftpd) + log(2l)`.
  * IV L1365-1376 (CΘ formula): `CΘ = (l+1)/(4·|log(q)|) · { (1+12 d_mod/l)(log(d_Ftpd)+log(f_Ftpd))
    + 10(e*_mod·l + η_prm) − (1/6)(1−12/l²)log(q) }` — the same shape as the R6/O(1)
    normalization `m/(n−3)` (both are degree-normalized O(1)-height comparisons).
- **OPEN CITATION**: the literal paper lines for the *local Weil function*
  `h_E <= m_i·h_{O(1)}` and its `m_i/(n−3)`-normalized `h_ω` form (as used in
  `R6LocalWeilData.hnorm`) are NOT in the IV.txt excerpts above; they belong to the
  local-height section of the (GenEll)/(D1) paper side (IV §2.3/§3 candidates).
  Please have andrew/Lead pin the exact lines before the docstring claims a paper line.

## 2. R6.2: `h_omega` comparison

- Current Lean: `hOmega` is a field of `R6LocalWeilData`; `ofProjHeight` sets
  `hOmega := (n−3)·hO1` making `hnorm` an identity, so R6.2 is *wired*, not *proved*,
  until the scheme-side omega height is identified with `(n−3)·hO1`.
- Paper: the `h_ω` object enters the CΘ/`log-cond` normalization (IV L1365-1376) and the
  height dictionary; an explicit paper-side identity for `h_ω` must be cited before
  claiming it (same OPEN citation as above).

## 3. R6.3: `h_E` identity

- Current Lean: `hE_eq : hE = m·hO1 − hP` is an *explicit field* (not an identification).
- The remaining identification (paper side) is: `h_E` = divisor height of the reduced `E_i`
  (with the completion-to-degree-`m_i` construction), i.e. `h_E = deg_{O(1)}(E_i)`.
  This is the same as the scheme `baseDiv`/`per-place metric` crosswalk; it must be carried
  as an explicit field/obligation (`hE_eq_divisor`, docstring citing the paper lines once
  located) rather than assumed.

## 4. Explicit fields/obligations still carried by R6 (andrew)

From `Mzk1HTF4R6Actual.R6LocalWeilData`:
- `n : ℕ`, `n_gt_three : 3 < (n:ℝ)` — curve degree input;
- `m : ℕ` — the homogeneous degree of the generators;
- `hO1 : ℝ` — O(1)-height value;
- `hP : ℝ`, `hP_nonneg : 0 <= hP` — multi-coordinate projective height `Height.logHeight x`;
- `hE : ℝ`, **`hE_eq : hE = m·hO1 − hP`** — the h_E definition (explicit);
- `hOmega : ℝ`, **`hnorm : m·hO1 = (m/(n−3))·hOmega`** — A4 normalization (explicit);
- `ofProjHeight` — concrete builder from `x : ι → K` (multi-coordinate, not Unit).

Still to identify (explicit fields/obligations, NOT proved):
1. completion-to-degree `m_i`: `hP = Height.logHeight x` must be the height of the
   completed generators of degree `m_i` (scheme-level completion map);
2. scheme `baseDiv`: `hE_eq` must be tied to the divisor of the reduced `E_i`
   (`hE = divisor height`), not just the algebraic expression;
3. per-place metric: `hOmega` must be tied to the local `ω`-height/metric normalization
   used in the CΘ formula (IV L1365-1376);
4. the local Weil function bound itself (`R6.1`) is conditional only through `hP_nonneg`,
   so it is closed *relative to the fields*; embedding into the main chain needs 1–3.

## 5. What would make R6 paper-faithful end-to-end

- Pin the local-height paper lines (OPEN above) and quote them in
  `R6LocalWeilData`/`hE_eq`/`hnorm` docstrings;
- Give the completion-to-degree and baseDiv crosswalk lemmas (from
  `Mzk1HTF4OrbitProductActual`/`Mzk1HTF4ActualInstanceActual` or the ported
  `WeilDivisor` donors) so `hP`/`hE` are the actual quantities;
- Then `hE_le_m`/`hE_le_kappa` become unconditional R6.1.

## PINNED OPEN CITATIONS (2026-11-18, from route + available paper texts)

### (a) R6: `h_E <= m_i·h_{O(1)}` and the `h_omega` normalization

Available in-repo paper anchor: IV L2557 says "... is the **local height** of E_F
[cf. **[GenEll], Definition 3.3**] for those v at which E_F has ...".  Hence the literal
`h_E <= m_i·h_{O(1)}` / `m_i/(n−3)` lines live in the **external [GenEll] paper
(Definition 3.3 and its local-height section)**, NOT in the repo's IUT text files;
searches for `n−3` / `hω` / `Weil function` / `logHeight` in III.txt/IV.txt return no
such literal lines.  Our route states the target shape in
`coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md`:
- L566: `h_ω + h_E <= (1+η)(D(L)+h_E) + C`;
- L569: `(1−ηκ)h_ω <= (1+η)D(L) + C`;
- L576: `h_ω(y) <= (1+δ)D(L) + C_{n,d,δ}`.
=> R6 docstring citation should be: [GenEll] Def 3.3 (local height) + route L566-576 for
the shape; do NOT claim a literal IV line for `h_E <= m_i h_{O(1)}` (none exists in repo).

### (b) R5: SeparationInput `B(p,d)` and local different / base = 0

Route `coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md` §7.1:
- L428: "通用局部域现在只补 SeparationInput 的实际实例";
- L430: UniversalSeparationToUFLEActual 仍接收 SeparationInput；后者才是当前出口;
- L437: "选**对所有 m<=d** 有效的 `B(p,d)`。不能直接以 `d(v_p(d)+1)` 替代 `m(v_p(m)+1)`，
  because `v_p` is not monotone; take a finite maximum, or the conservative `d(d+2)`.";
- L439: fill SeparationInput, then call the existing explicit N / coefficient finite-ization /
  Krasner / universal field assembly.
The base-different-zero fact is the local instance `differentIdeal_self_eq_top` (base
different = 0 for the base field itself) used to fill the local field data; route §7.1
keeps it as the actual instance rather than a prerequisite (see route L430-439 context).
=> R5 docstring citation: route §7.1 L428-439; paper source for B(p,d) is the local-field
separation input of the generalized-elliptic-curve / universal local field construction
(not literally present in the repo IUT texts → cite route lines, do not invent IV lines).

### (c) R7: F7 three classes + `D(L) <= log rad(abc) + C_n`

Route `coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md` §9.1:
- L584: "现在保留的 F7 任务是实际域的 ramification 实例";
- L586: existing fermatRoot / minpoly degree bound / global discriminant sum / tame count
  upper bound / wild normalized algebra cannot directly give F7 for the actual fermatLiftL;
- L594: "随后按实际素数分三类" (three classes of primes);
- L602: **`D(L) <= Σ_{p | abc} log p + C_n`**;
- L613: "对每个三元组，使用 9.1 的同一个 L 和同一个 y".
Also route L82: `D(L) = log|disc L|/[L:Q]`; L273: `h̄_L(λ) <= (1+η)(D(L)+N_L(λ)) + C`;
L345: `D(F_tpd)+N_Ftpd(λ) <= D(L)+N_L(λ)`.
=> R7 docstring citation: route §9.1 L584-613 (+ L82/L273/L345); the paper side is the
Fermat/abc height dictionary (external; not present literally in repo IUT texts).


## R7 exact names (added 2026-11-18)

- `Mzk1G1F7LiftDegreeActual.fermatLiftL_finrank_le_sq :
  Module.finrank ℚ (fermatLiftL n hn a b c) <= n*n` (R7 `[L:Q] <= n^2`);
- `Mzk1G1F7LiftDegreeActual.{isIntegral_fermatRoot, finrank_adjoin_singleton_le_of_pow_eq,
  fermatLiftL_finiteDimensional}`;
- `Mzk1G1DifferentBoundConservativeActual.{differentBoundConservative (d)=d*(d+2),
  padicValNat_le_self, differentBound_le_conservative, differentBoundConservative_pos}`
  (R5 B(p,d) conservative form = route §7.1 L437).

### R7 F7 status correction (2026-11-18 17:45)
`Mzk1G1F7LiftDegreeActual` FAIL 17:45:33 (statement issue hy : y^m = algebraMap q); earlier 17:06 DONE superseded. `Mzk1G1F7LiftTowerActual` FAIL 17:45:07 (type mismatch L26). `Mzk1G1F7LiftActual` DONE 14:22:04 remains the valid R7 anchor; do not cite LiftDegree as current.

### 2026-11-18 17:55 R4/R7 additions

- R4 psi_structure: `Mzk1G1R4ProtectedActual.ProtectedPointData.psi_structure`
  (route §6.2(iv): psi⁻¹(0)=supp D, 0∉psi(S), 0∉Branch psi) + `fiberAboveZero`,
  `unramifiedOverZero`; `ProtectedPointData` carries S/T/D/s0/s1/psi + support side
  conditions.  Note the flt_core vs flt root split (mirrors used).
- R7 F7 corrected: only `Mzk1G1F7LiftActual` (DONE 14:22:04) is valid;
  `Mzk1G1F7LiftDegreeActual` FAIL 17:45:33 and `Mzk1G1F7LiftTowerActual` FAIL 17:45:07.

### 2026-11-18 18:00 F7 latest: Mzk1G1F7LiftDegreeBasicActual DONE 18:00:32 but only isIntegral_fermatRoot + fermatLiftL_finiteDimensional; `fermatLiftL_finrank_le_sq` ([L:Q]<=n^2) is NOT present. LiftDegree FAIL 17:45:33; LiftTower FAIL 17:45:07; only F7LiftActual DONE 14:22:04 valid. R7 [L:Q]<=n^2 currently NOT proved.
### 2026-11-18 18:08 F7 audit: LiftDegreeBasic source (mtime 18:05:51) now contains fermatLiftL_finrank_le_sq ([L:Q]<=n^2) + finrank_adjoin_singleton_le_of_pow_eq; last DONE 18:00:32 is stale, recompile START 18:08:20 in flight. LiftTower still FAIL 17:45:07. R7 [L:Q]<=n^2 restoration in progress.
### 2026-11-18 18:09 R7 RECOVERED: Mzk1G1F7LiftDegreeBasicActual re-DONE 18:09:13 with fermatLiftL_finrank_le_sq (finrank ℚ (fermatLiftL n hn a b c) <= n*n) and finrank_adjoin_singleton_le_of_pow_eq; [L:Q]<=n^2 recovered. LiftTower still FAIL; LiftDegree superseded.
### 2026-11-18 18:12 recompile verification: F7LiftDegreeBasic re-DONE 18:09:13 (mtime 18:05:51 < DONE, consistent) with fermatLiftL_finrank_le_sq -> R7 [L:Q]<=n^2 recovered, no stale olean.
### 2026-11-18 18:41 R7: new file Mzk1G1F7PrimeClassesActual in flight (f7_tame_delta_eq_ramification_sub_one, f7_wild_contribution_le, F7PrimeClassContributionData, DL_le_sum_bound) = §9.1 three-class machinery; verify on DONE.
### 2026-11-18 18:52 F7PrimeClasses tail: FAIL type mismatch (expected differentExponent P = e-1 in f7_tame_delta_eq_ramification_sub_one); f7_wild_contribution_le and DL_le_sum_bound axiom prints clean.
### 2026-11-18 19:02 R7 F7PrimeClasses DONE: Mzk1G1F7PrimeClassesActual (3 decls: f7_wild_contribution_le, F7PrimeClassContributionData, DL_le_sum_bound; clean trio, no sorry). Tame-delta standalone theorem removed; tame clause from donor F7TameMonogenicActual.differentExponent_eq_ramification_sub_one_of_monogenic. Remaining R7: apply to actual Fermat lift L (same L/y per route L613). Watchdog restarted DAG_MAX=4.
### 裁定 2026-11-18 19:26: R6 引 IV:3172 勘误（不是 [GenEll] 3.3 等式）；R7 F8 高度锚点 n*hbar_L(P)=log c。
