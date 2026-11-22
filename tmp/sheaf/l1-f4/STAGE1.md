# L1-F4 Stage 1/2: Source theta divisor boundary

- package: `L1-F4`
- owner file: `LeanFormal/IUT/IUTII/Frobenioid/Example36SourceThetaDivisor.lean`
- stage: 1 (scope and exact boundary) / 2 (next statement)
- current source: 810 lines, SHA256 `3D49106992D4BCFBC630179F0F8552652AF586631E9143E83D5AA422AEA17BA8`
- production edits in this task: none.

## Source target

Motizuki, *The Etale Theta Function and its Frobenioid-theoretic
Manifestations*, Proposition 1.4 (i), (ii), (iii); IUT II theta evaluation and
q-expansion; IUT I Definition 3.6 and Corollary 3.7.

The file's own audit obligation records the status as
`VerificationStatus.testCarrier` and explicitly separates the even theta
q-series from the source odd theta divisor.

## What is currently proved (kernel-checked in the production module)

Build evidence: serialized wrapper
`build LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor` exited 0
(8839 jobs). No `sorry`/`admit`/`axiom` token in the source.

1. Analytic carrier normalisation and q-expansion
   - `carrierThetaTau`, `carrierThetaTau_im`, `carrierThetaTau_im_pos`,
     `carrierThetaTau_core`, `carrierThetaTau_exp`;
   - `carrierTheta_term_eq`;
   - `analyticThetaValue`, `analyticThetaValue_eq_tsum_nat`.
2. Nonvanishing and positivity
   - `thetaRealValue`, `summable_thetaNatTerm`, `thetaNatSum_pos`,
     `thetaRealValue_pos`;
   - `analyticThetaValue_eq_ofReal`, `analyticThetaValue_ne_zero`;
   - `analyticThetaValue_concrete_eq_jacobiThetaQ`,
     `analyticTheta_ne_zero_concrete`.
3. Principal unit / q-adic order zero
   - `thetaQAdicQuotient`, `summable_thetaQAdicQuotientTerm`,
     `thetaQAdicQuotient_pos`, `thetaQAdicQuotient_ne_zero`;
   - `thetaRealValue_eq_one_add_q_mul`,
     `analyticThetaValue_eq_one_add_q_mul`,
     `jacobiThetaQ_eq_one_add_q_mul`;
   - `gaussianThetaCoeff`, `gaussianThetaFormalSeries`,
     `gaussianThetaFormalSeries_constantCoeff`,
     `gaussianThetaFormalSeries_isUnit`, `gaussianThetaFormalSeries_order`.
4. Even theta zero divisor on the q-disc
   - `analyticThetaZeroSet`, `analyticThetaZeroSet_empty`,
     `analyticThetaDivisor_trivial`.
5. Theta units and root values
   - `thetaQUnit`, `thetaUnit`, `thetaUnit_eq_qUnit_pow`,
     `thetaUnit_neg`, `thetaUnit_zero`, `realThetaValue_pow_q`,
     `thetaUnit_transport`, `thetaUnit_concrete_packetScale`;
   - `thetaRootValue`, `thetaRootValue_twoLth_root`,
     `thetaRootValue_sq`, `thetaRootValue_mul_root_of_pow_eq_one`,
     `thetaRootValue_neg_root`, `thetaRootValue_sqrt_concrete_sq`,
     `thetaRootValue_sqrt_concrete_sq_complex`;
   - `normalizedTheta`, `normalizedTheta_apply`,
     `normalizedTheta_eq_thetaUnit`, `normalizedTheta_orbit_compatible`.
6. Odd theta order-zero special fibre
   - `oddThetaOrderZeroPart`, `oddThetaOrderZeroPart_eq`,
     `oddThetaExponent_eq_zero_iff`,
     `oddThetaExponent_pos_of_ne_zero_of_ne_neg_one`,
     `oddTheta_qAdic_orderZero_reduction`;
   - `oddThetaReduction_factorization`, `oddThetaReduction_eq_zero_iff`,
     simple zero factors at `±1`, `oddThetaReduction_pole_at_zero`,
     `oddThetaReduction_pole_value` (simple pole at 0).
7. Summary and audit
   - `example36SourceThetaDivisor_summary` packages the above conjunction;
   - `example36SourceThetaDivisor : Obligation` with testCarrier status.

## Exact current boundary (not proved)

From the module documentation and audit note:

- (a) convergence/reindexing of the full two-sided nonarchimedean odd theta
  series `sum_{n in Z} oddThetaTerm q U n`. `Foundations/Theta/OddTheta.lean`
  currently proves only the forward half
  `summable_oddThetaTerm_nat`; the negative half and two-sided sum are open.
- (b) the shift law
  `Theta(q^(a/2) U) = (-1)^a q^(-a^2/2) U^(-2a) Theta(U)` for a supplied
  square root of q, and nonvanishing of the odd theta at `U = i`
  (EtTh Proposition 1.4 (ii)).
- (c) meromorphic continuation of the odd theta function to the Tate curve
  `Yddot`, with zero divisor precisely the cusps of multiplicity one and pole
  divisor precisely `D_1` (EtTh Proposition 1.4 (i)).
- (d) identification of the Kummer classes of Proposition 1.3 with theta
  values (`O_K^times`-multiples), i.e. the actual etale theta function, the
  line-bundle section, and the nontrivial source Theta-link
  (EtTh Proposition 1.4 (iii)).

Important scope note: the empty zero divisor proved for the even theta
q-series in Section 3 is NOT the source odd theta divisor. No q-series
coefficient comparison is claimed to establish (c) or (d). The file contains
no Kummer class, no theta line bundle, and no source Theta-link object.

## Consumer audit

- `LeanFormal/IUT/Project.lean` imports this module once. The import supplies
  the audit `Obligation` record; it does not expose a theorem-level Theta-link
  consumer.
- There is no current file that imports `Example36SourceThetaDivisor` and uses
  its declarations in a Theta-link proof. In particular:
  - `IUTII/Theta/ThetaLinkAssembly.lean` is an abstract algebraic
    unit-generated-monoid comparison; it does not import this module and does
    not identify the analytic theta function, source theta divisor, or Kummer
    class.
  - `IUTII/Theta/ConcreteSourceEtaleThetaBridge.lean` and
    `ConcreteSourceHistoryLinkBridge.lean` do not import this module; their
    source models are separate frozen cards.
  - `IUTII/Theta/EtaleThetaQuotient.lean` is an obligation-level statement,
    not an analytic-theta consumer of this file.
- Upstream dependencies actually used: `Example36SourceThetaGenerator`,
  `Example36ThetaSeries`, `Foundations/Theta/OddTheta`,
  `Mathlib.RingTheory.PowerSeries.Order`,
  `Mathlib.RingTheory.PowerSeries.Inverse`.
- Downstream status: package is Project/audit-visible only; no source
  Theta-link consumer currently depends on it.

## Minimal next provable declaration

The smallest statement that closes a real gap and is independent of the
missing geometric/Kummer content is the negative half of the odd theta
summability in `Foundations/Theta/OddTheta.lean`:

```lean
theorem summable_oddThetaTerm_neg_nat
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => oddThetaTerm q U (-(n : ℤ) - 1))
```

Proof route (uses only already-green ingredients):

1. For `n : ℕ`, `oddThetaExponent (-(n+1)) = n * (n+1) / 2` by
   `oddThetaExponent_coe`/`Int.toNat_of_nonneg`.
2. `norm_oddThetaTerm` gives
   `‖oddThetaTerm q U (-(n+1))‖ =
     ‖U‖⁻¹ * (‖q‖ ^ (n * (n+1) / 2) * (‖U‖⁻²) ^ n)`
   after rewriting `U ^ (-(2n+1)) = (U⁻¹) ^ (2n+1)` and separating
   `‖U‖⁻¹ * (‖U‖⁻²)^n`.
3. Apply `tendsto_quadraticExponential_mul_geometric` with
   `a = ‖q‖`, `b = ‖U‖⁻² > 0`, then
   `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` with
   `Nat.cofinite_eq_atTop`, exactly as in `summable_oddThetaTerm_nat`.

Immediate follow-on statement (separate node):

```lean
theorem summable_oddThetaTerm
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => oddThetaTerm q U n)
```

This follow-on splits `ℤ` into nonnegative and negative indices and combines
`summable_oddThetaTerm_nat` with `summable_oddThetaTerm_neg_nat`; the exact
Mathlib two-sided-sum lemma should be selected in stage 2 before stating the
final proof.

These statements close only gap (a) (well-definedness of the two-sided odd
theta series). They do not assert the shift law, odd-theta nonvanishing,
meromorphic continuation/divisor, Kummer class, or Theta-link.

## Stage 2 acceptance boundary for the minimal statement

- statement_compiles: not yet recorded (this stage writes no Lean declaration).
- proof_body_checked: not yet.
- kernel_closed: not yet.
- target_accepted: not yet.
- no production file changed in this stage.

## Node-local stage and child nodes

Per the fractal-stage rule, stages are local to a DAG node; no global stage
barrier is assumed.

- Parent node L1-F4 (owner file SourceThetaDivisor.lean)
  - local stage: 1 and 2 delivered by this document
  - state: OPEN / not closed; no production declaration changed here
  - reason: the minimal next real gap (two-sided odd theta summability) is not
    a declaration of this owner file.
- Child node L1-F4.a (stage 2/3, proof checked)
  - target file: Foundations/Theta/OddTheta.lean (not owned by this package)
  - declaration: summable_oddThetaTerm_neg_nat, the negative half of the odd
    theta series
  - dependencies: oddThetaTerm, oddThetaExponent_coe, norm_oddThetaTerm,
    tendsto_quadraticExponential_mul_geometric,
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero;
    all cited ingredients are green in OddTheta.lean
  - implementation: tmp/sheaf/l1-f4/OddThetaSummable.lean
    (64 lines, SHA256 BBB9C8B0F1B9B120EDA5C51AB4EC7DA0890D7F82BF28C0A7A5911EEA544E84ED)
  - evidence: lake env lean exit 0; no sorry/admit/axiom; statement_compiles,
    proof_body_checked, kernel_closed for the temp candidate; production
    integration/axiom audit not run
- Child node L1-F4.b (stage 3, proof checked)
  - target file: Foundations/Theta/OddTheta.lean
  - declaration: summable_oddThetaTerm, the full two-sided integer-indexed odd
    theta series
  - dependency: L1-F4.a proof plus Mathlib Summable.of_nat_of_neg_add_one
  - implementation: now integrated into production
    LeanFormal/IUT/Foundations/Theta/OddTheta.lean (new owner)
  - declarations added: oddThetaExponent_neg_nat, norm_oddThetaTerm_neg_nat,
    summable_oddThetaTerm_neg_nat, summable_oddThetaTerm; existing
    summable_oddThetaTerm_nat preserved
  - production evidence: targeted build
    LeanFormal.IUT.Foundations.Theta.OddTheta exit 0 (8655 jobs); final file
    360 lines, SHA256 F2E7BF7CE0CC54529D6DD956CAF1032F6C849FC2E9B2DAE40B60ADC8BEA35B0C,
    no sorry/admit/axiom
  - status: proof_body_checked=true in production; transitive axiom audit and
    consumer integration into SourceThetaDivisor not yet run

Parent SourceThetaDivisor work remains unclosed until L1-F4.a and the
two-sided series are available and the corresponding consumer statement in the
owner file is added.
## Axiom probe evidence (2026-10-22)

- Probe: tmp/sheaf/l1-f4/AxiomProbe.lean (12 lines, SHA256 049E4D03DD8AC0FD152B5B27FC597DC446DEE8CAB0886660B3F42094DA248F74).
- lake env lean exit 0; log tmp/sheaf/l1-f4/axiom-probe.log.
- All four production declarations depend only on [propext, Classical.choice, Quot.sound]:
  oddThetaExponent_neg_nat, norm_oddThetaTerm_neg_nat, summable_oddThetaTerm_neg_nat, summable_oddThetaTerm.
- Production OddTheta.lean: 360 lines, SHA256 F2E7BF7CE0CC54529D6DD956CAF1032F6C849FC2E9B2DAE40B60ADC8BEA35B0C; declaration lines 255, 263, 279, 301.
- Targeted build evidence: 8655 jobs, Build completed successfully, EXIT=0.

