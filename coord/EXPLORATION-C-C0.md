# C0 targets: ind2Term and archDefect (A918)

## 1. Source-level derivation (what was done)

Read lana `Iut/WallEquiv/Gap.lean` (root tree; oleans being built by mainline):
- `ind2Term` (:747-754) = `componentVol (leastHull (thetaComponent)) -
  componentVol (scaleElt * leastHull (shell))`; `ind2Term_nonneg` (:756);
  `ind2Term_eq_zero` off bad chars (:771); `gapHullAt` (:895) = sum_c w_c * ind2Term;
  `gap_eq` (:961); header (:30-36): `tensorAut` = Z_p-lattice automorphisms of factor
  log-shells, 'need not commute with theta values'; sign at bad primes OPEN.
- `archDefect` (:459) = `componentVol (leastHull (logShell)) - componentVol (logShell)`;
  `archDefect_nonneg` (:463); exact value `log((2^{N-1})!)/2^N` at :66, NOT formalized.

Machine file: `tmp/sheaf/xif/paper/Mzk1C0TargetsActual.lean` (EXIT=0, olean, trio):
- **T1** `ind2Term_eq_scaling_add_defect`: from `ind2 = thetaHullLog - scaledHullLog`,
  `thetaHullLog = base + (j^2 v_p(q)/(2l)) logp + defect`, `scaledHullLog = base`,
  conclude `ind2 = (j^2 v_p(q)/(2l)) logp + defect` (PROVED, arithmetic);
- **T1'** `ind2Term_frac_form`: defect = frac*logp form (PROVED conditional);
- **T2** `archDefect_eq_formula`: from `archDefect = leastHullLog - shellLog` and the
  orthogonality identity `leastHullLog = shellLog + log((2^{N-1})!)/2^N`, conclude the exact
  value (PROVED conditional);
- predicates `TensorMetricOrthogonality`, `TensorAutCommutationDefect` = the exact lana inputs.

## 2. Data table

| target | statement | status |
|---|---|---|
| T1 | ind2 = (j^2 v_p(q)/(2l)) logp + defect | PROVED conditional |
| T1' | ind2 = ((j^2 v_p/(2l)) + frac) logp | PROVED conditional |
| T2 | archDefect = log((2^{N-1})!)/2^N | PROVED conditional |
| tensorAut commutation defect | theta hull = base + scaling + defect | GAP (lana) |
| tensor-metric orthogonality | leastHullLog = shellLog + formula | GAP (lana) |

## 3. Comparison with C0 judgment conditions

- C0(a) ind2Term formula: the derivation needs exactly two lana inputs — the exact
  `componentVol leastHull` formula (`componentVol_leastHull_tensorLogShell_eq`) plus the
  tensorAut/theta commutation defect.  With them, T1/T1' give the fractional-part formula.
- C0(b) archDefect exact value: needs the tensor-metric orthogonality (lana gap, stated in
  Gap.lean:66); T2 then gives the exact value.  Nonnegativity already proved in lana (:463)
  and in our model (`Mzk1C0Ind2ArchActual.archDefect_model_nonneg`).
- No sorry/axiom/assumption replacing a proof: the missing lana inputs are explicit
  predicates/hypotheses; the file stops at the judgment point.

## 4. Next step

1. Use mainline's `Iut/WallEquiv/Gap.lean` olean to import `ind2Term`, `gapHullAt`, `gap_eq`;
2. Prove `thetaComponent` closure over `tensorAut` images and the commutation defect
   (`TensorAutCommutationDefect`), then instantiate T1/T1';
3. Prove `TensorMetricOrthogonality` from component orthogonality, then instantiate T2;
4. Evaluate the sign of `gapHullAt` at bad primes (C0 judgment).

## 5. A922 audit completion (Status line, touchstone, judgment, E-class registration)

**Status: PARTIAL** — conditional target theorems T1/T1'/T2 are green; two lana lemmas are
not formalized (see E-class below).

**Touchstone answer (C0 = calculator-evidence stage)**: this stage contains NO inequality
claim.  All results are CONDITIONAL on explicit predicates; the quantifier/information-entry
declaration is: 'no `forall D` inequality, no numerical bound asserted; not applicable /
deferred (本轮不含不等式主张，不适用/暂缓)'.

**Judgment sentence**: C0 = PARTIAL，停在该判定点.

**E-class external/waiting dependencies (registered):**
- E-C0-1 `TensorAutCommutationDefect` — tensorAut Z_p-lattice action vs theta exchange defect
  (external, to prove with lana `Iut/WallEquiv/Gap.lean` + `Concrete/LocalConstruct/*`);
- E-C0-2 `TensorMetricOrthogonality` — leastHullLog = shellLog + log((2^{N-1})!)/2^N
  (external, lana orthogonality of tensor-metric components);
- E-C0-3 `componentVol_leastHull_tensorLogShell_eq` — exact hull volume
  `sum_j rho_{cj} log p` (external, lana VcI/FinitePadic*).
