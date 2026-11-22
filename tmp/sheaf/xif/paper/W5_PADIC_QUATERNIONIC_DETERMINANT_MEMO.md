# W5: p-adic / quaternionic determinant and Monge-Ampère analogues for the least λO hull

Date: 2026-10-30. Task W5. Status: **new p-adic determinant construction + Lean, plus explicit no-go for the quaternionic/Monge-Ampère transplant**. No target change, no surrogate, no fake object, no new axiom.

Companion Lean file: [S822PadicDetHullActual.lean](S822PadicDetHullActual.lean).
Read first: [TASK_LEDGER.md](TASK_LEDGER.md), [S743_LOCAL_SMOOTHING_QUATERNION_MEMO.md](S743_LOCAL_SMOOTHING_QUATERNION_MEMO.md) (Task P), [S793PaperLeastLambdaOHullActual.lean](S793PaperLeastLambdaOHullActual.lean), [S782FiniteRootStackExtensionActual.lean](S782FiniteRootStackExtensionActual.lean), [S779RootHullNonzeroFixActual.lean](S779RootHullNonzeroFixActual.lean).

## 0. One-paragraph answer

A genuine p-adic determinant **does** exist and is already the engine of the repo's exact hull-log computation: the Haar scaling character `MeasureTheory.distribHaarChar` (Mathlib, `MeasureTheory/Measure/Haar/DistribChar.lean`), i.e. the modulus `|det|_p` of a multiplicative action. I packaged it as `padicDet` and proved the identity **log-volume of a scaled canonical lattice = log of the p-adic determinant** (`normalizedLogVolume_smul_canonicalUnitReference`). This yields a sharp structural fact: the p-adic determinant is a monoid homomorphism, so its log is **additive in the exponent**; the normalized log-volume of the least λO family is *affine* in the coefficient, and the p-adic Monge–Ampère operator (second difference) **vanishes identically** (`normalizedLogVolume_secondDifference_zero`). Concavity therefore degenerates to equality — there is no p-adic analogue of the strict concavity of log det that the archimedean MA argument uses. For the paper coefficient `order/(2l)`, the determinant has a canonical `2l`-th root only after passing to the finite root stack: in the completion the relevant generator is a value-group question (and concretely `p` has no square root in `Q_p`, formalized in `padic_no_sqrt_prime`), while the actual root-stack unit has norm `p^{-c_norm/(2l)}` with `c_norm` the *spectral normalized coefficient*, not the paper order ([S817](S817StackRootUnitNormActual.lean), [S121](S121QVFamSpectralValuationActual.lean)); so the determinant route lands exactly on the known normalization gap, not around it. The quaternionic/Monge–Ampère transplant is a **no-go** for concrete reasons: (i) the actual root stack is cyclic `μ_{2l}` with `l` odd, so it contains no order-4 element and hence no quaternionic `i` (formalized: `no_mu2l_sqrt_neg_one`); (ii) the hull carrier is a commutative one-factor `Q_p`-algebra, so a quaternionic module structure would be extra data with no map to the hull (a fake object if posited); (iii) any p-adic quaternionic determinant (Dieudonné determinant / reduced norm) is a scalar `K^×`-valued invariant whose modulus is again the same Haar scaling character, so it cannot produce a second invariant; (iv) the Moore determinant's positivity/real-eigenvalue theory has no p-adic positive cone, and the non-archimedean MA of Berkovich/Chambert-Loir has no comparison theorem to the procession-normalized IUT hull log (already rejected in S728). **Verdict: p-adic determinant = real tool, but it does not close any current exact gap; quaternionic MA = no-go.**

## 1. The p-adic determinant: definition and the exact theorem

### 1.1 Definition (actual, not a model)

For a locally compact additive group `A` with additive Haar `μ` and a group `G` acting by additive automorphisms, Mathlib defines

    `distribHaarChar A : G →* ℝ≥0`,   `μ (g • s) = distribHaarChar A g * μ s`

(`Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:43` and `:83`). For `A = qVFamTensorBlock T b` (a finite-dimensional `Q_p`-algebra) and `G = Aˣ`, this number is the p-adic modulus of multiplication by `u` — the exact p-adic analogue of `|det|`. In the file:

* `padicDet (μ) : (qVFamTensorBlock T b)ˣ →* ℝ≥0 := MeasureTheory.distribHaarChar _`;
* `padicDet_pos`, `padicDet_mul`, `padicDet_pow`.

### 1.2 The determinant ↔ log-volume identity (new)

`normalizedLogVolume_smul_canonicalUnitReference`: for every unit `u` (with `μ` a regular additive Haar; the Lean statement carries `[Measure.Regular μ]`, which is the standard regularity of the canonical Haar, not re-proved here),

    `V(u • O) = (1 / [K : Q_p]) * Real.log (padicDet μ u)`,

where `V` is the IUT IV Proposition 1.4(i) degree-normalized log-volume (`arithmeticTupleNormalizedLogVolume`, `FinitePlaceNormalizedUnitScalingLogVolume.lean:92`) and `O` is `arithmeticTupleCanonicalUnitReference`. Proof: `μ(u•O) = Δ(u) μ(O)` (`distribHaarChar_mul`), then `Real.log_mul`. This is the exact p-adic statement "log-volume = log det", and it is the right general form of the computation that the repo previously did only through the common-exponent trick (`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`, same file `:379`).

### 1.3 Z-linearity in the exponent and roots of the determinant (new)

`normalizedLogVolume_smul_pow`: `V((u^n) • O) = n · V(u • O)`.
`normalizedLogVolume_smul_eq_of_pow_eq`: if `v^n = u` then `V(u • O) = n · V(v • O)`.

This is the only precise sense in which a "`2l`-th root of the determinant" exists. It also shows that the determinant is **blind to the branch**: it sees only the exponent vector, not which root was chosen (the `μ_{2l}` ambiguity cancels in the log).

## 2. p-adic Monge–Ampère: the operator is identically zero

Define the hull-log functional on coefficients `c : qVFamTensorV → ℝ` by

    `hullLogFunctional c = - (∑ i, c i) * log p`.

Then (`hullLogFunctional_add`, `..._zero`, `..._smul`) it is additive, vanishes at `0`, and is `ℝ`-homogeneous. On the data locus (coefficients admitting `ArithmeticTuplePureFractionalScalingData`), the *actual* normalized log-volume equals it (`normalizedLogVolume_lambdaOSet`), and the data locus is closed under addition and contains zero, constructively:

* `arithmeticTuplePureFractionalScalingData_add`: from data at `c` and at `c'`, build data at `c + c'` using the product of the actual local generators, `‖g_i g'_i‖ = p^{-(c_i + c'_i)}` (via `arithmeticTuplePureFractionalScalingData_ofGenerator`);
* `arithmeticTuplePureFractionalScalingData_zero`: data at `0` from the unit generator `1`.

Consequently (`normalizedLogVolume_lambdaOSet_add`, `..._zero`, `normalizedLogVolume_secondDifference_zero`):

    `V(c + c') = V(c) + V(c')`,  `V(0) = 0`,
    `V(c + c') - V(c) - V(c') + V(0) = 0`.

So the p-adic "Monge–Ampère operator" `det(∂²V/∂c_i∂c_j)` is zero. This is not a defect of the formalization: it is the exact content of "Haar measure scales by a character". The archimedean MA argument uses **strict concavity** of `log det` on the positive cone (and Brunn–Minkowski log-concavity of volumes) to obtain uniqueness/comparison/Jensen inequalities; p-adically the same functional is affine, so:

* every concavity statement is an **equality**, not an inequality;
* the label average of S694 (`l*` classes, weight `1/l*`, exponent `j²/(2l)`) satisfies Jensen with equality, so it produces no new inequality for the target `qPilotLog ≤ hullLog`; it is already implied by the exact formula;
* no strict curvature term can be extracted to separate the two sides.

At the level of sets the analogy fails even more strongly (prose, not formalized here): the least λO hull is an *intersection* of candidate regions (a min-like operation, [S793](S793PaperLeastLambdaOHullActual.lean)), not a Minkowski interpolation, and in an ultrametric space `B(0,r) + B(0,r') = B(0,max r r')`, so log-volume of a Minkowski interpolation is max-like (convex, not concave). The concrete value-group manifestation is `padic_no_sqrt_prime` (Lean): `p` has no square root in `Q_p`, so a coefficient cannot be halved inside the completion — a midpoint concavity step needs the root stack.

## 3. The 2l-th root and the root stack: where the determinant stops

The paper coefficient is `c* = order/(2l)` ([QVFamRootFactorCorrectionActual.lean:56](QVFamRootFactorCorrectionActual.lean)); `paperRootCoefficient_twoL_mul` proves `(2l) · c* = order`. The paper hull log would be `-c* log p`.

* **Completion side.** `ArithmeticTuplePureFractionalScalingData` at `c*` needs a local generator of norm `p^{-c*}` (S815 reduces `Nonempty data` exactly to this). The value group of the completion is `(1/e)Z`, so this needs `2l | e·order`; in particular it can fail. This is why S809/S812/S815 are conditional. `padic_no_sqrt_prime` is the simplest instance of the obstruction.
* **Root-stack side.** [S782](S782FiniteRootStackExtensionActual.lean) builds the finite `L(μ_{2l})` and the root section satisfying `stackRootSection^(2l) = stackQSection`, with divisor coordinate `order/(2l)`. But [S817](S817StackRootUnitNormActual.lean) proves the *actual* norm of that root unit is `p^{-c_norm/(2l)}` with `c_norm` the spectral normalized coefficient, and [S121](S121QVFamSpectralValuationActual.lean:60) gives `c_norm = exponent·deg - log(normRatio)/log p`; [S817](S817StackRootUnitNormActual.lean) also proves `‖stackRootUnit‖ = p^{-order/(2l)}` **iff** `c_norm = order`.

So the determinant gives the paper hull log only after (a) the carrier/measure transport of S812 and (b) the source normalization identity `c_norm = order`. That identity is an arithmetic normalization statement about the actual qVFamily generator — not a determinant identity, and not something the determinant can supply. The p-adic determinant therefore *localizes* the remaining gap instead of closing it.

**Exact statement of what is and is not obtained.** Given the root `v` in the finite extension with `v^{2l} = q`, the determinant gives the log-volume of the root-scaled lattice *on that extension* as `(1/(2l))·log Δ(q)`; to identify it with the paper tensor-block hull log one still needs (a) the carrier/measure transport of [S812](S812LeastLambdaOFiniteLStackActual.lean)'s `PaperLeastHullFiniteLHaarBridge` and (b) the normalization `c_norm = order`. The file asserts neither.

## 4. Quaternionic Monge–Ampère: no-go

The archimedean Task-P proof uses `H`-Hermitian matrices, the Moore determinant (product of real eigenvalues with quaternionic multiplicity), a positive cone, quaternionic Hessians of `C²` functions and a divergence-form cofactor identity. Each ingredient needs a real/complex vector space with an inner product and an open positive cone. Against the actual paper objects:

1. **No order-4 torsion.** `l` is an odd prime (`l ≥ 5`), so `2l ≡ 2 (mod 4)`. If `ζ^{2l} = 1` and `ζ² = -1`, then `1 = ζ^{2l} = (ζ²)^l = (-1)^l = -1`, forcing `2 = 0` in a characteristic-zero field. Formalized as `no_mu2l_sqrt_neg_one`, and on the actual finite root-stack extension as `rootStack_no_mu2l_sqrt_neg_one`. Hence the root stack cannot supply the quaternionic units `i, j, k`.
2. **No carrier.** The hull lives in `qVFamTensorBlock T b`, a commutative one-factor `Q_p`-algebra (`qVFamTensorV = Unit`). A quaternion-division-algebra module structure on it would be additional structure with no construction from the source; positing one is exactly the kind of fake object the project forbids.
3. **The determinant is still scalar.** For a quaternion division algebra `D/Q_p`, the Dieudonné determinant / reduced norm `Nrd` takes values in `Q_p` and its modulus is the Haar scaling character of the `Q_p`-linear multiplication map. So even a genuine p-adic quaternionic determinant adds no invariant beyond `padicDet`; it cannot distinguish the paper coefficient from its sum or detect a concavity.
4. **No positivity/MA comparison.** The Moore determinant's real eigenvalues and positivity come from the real closed field; `Q_p` is not real closed, Hermitian forms have no open positive cone, and the non-archimedean Monge–Ampère measure of Berkovich/Chambert-Loir has no theorem identifying it with the procession-normalized Haar log (S728 already rejected that route for the same missing comparison).

Therefore there is no honest way to state a quaternionic MA theorem about the least λO hull with the current objects. This is a *construction no-go*, not a claim that p-adic quaternionic linear algebra does not exist: it exists, but it is scalar-equivalent to the p-adic determinant and has no carrier map to the paper hull.

## 5. Effect on the actual gap

| Current exact gap | Does W5 reduce it? | Reason |
|---|---|---|
| `ConcreteSourceQIdentification` (`sourceQPilotSignedLog = localSignedLog C3.q`) | No | A determinant computes a volume from a given norm; it cannot identify a source element. |
| qPilot → product-hull containment / log comparison | No | The log-volume side is already exact on the data locus (S799/S801/S812); the missing piece is the hull/carrier comparison, not a determinant identity. |
| Paper hull equality `rootExtensionProductImageHull = paper λO hull` | No | Set equality of carriers; the determinant only gives equality of volumes *after* a measure-preserving transport (S812 bridge). |
| `PaperXiFSourceLink` fields | No | All four are source/link identifications; none is a log-volume computation. |
| `PaperLeastHullLogFormulaTarget` / hull-log formula | **Already exact conditional on data** | `paperLeastLambdaOHullLog_eq_formula` (S799). W5 re-derives it as "log det" and adds the root/normalization analysis. |
| `c_norm = order` normalization | **Located, not closed** | S817/S121; this is the exact statement the determinant reduces to. |

In short: the p-adic determinant is not a new route around the gap — it is the *reason* the hull-log side is already closed. The remaining gaps are source/normalization/carrier identifications, and a determinant cannot manufacture them.

## 6. Lean: declarations and status

File `S822PadicDetHullActual.lean` (imports S793, S799, S782, the value-group constructor, Padic norm):

* `padicDet`, `padicDet_pos`, `padicDet_mul`, `padicDet_pow`;
* `normalizedLogVolume_smul_canonicalUnitReference`;
* `normalizedLogVolume_smul_pow`, `normalizedLogVolume_smul_eq_of_pow_eq`;
* `hullLogFunctional`, `hullLogFunctional_add`, `hullLogFunctional_zero`, `hullLogFunctional_smul`;
* `arithmeticTuplePureFractionalScalingData_add`, `arithmeticTuplePureFractionalScalingData_zero`;
* `normalizedLogVolume_lambdaOSet`, `normalizedLogVolume_lambdaOSet_add`, `normalizedLogVolume_lambdaOSet_zero`, `normalizedLogVolume_secondDifference_zero`;
* `paperRootCoefficient_twoL_mul`, `hullLogFunctional_twoL_mul`;
* `no_mu2l_sqrt_neg_one`, `rootStack_no_mu2l_sqrt_neg_one`;
* `padic_no_sqrt_prime`.

### Compile evidence (actual, 2026-10-30)

Command: `lake env lean tmp/sheaf/xif/paper/S822PadicDetHullActual.lean`, from `D:\lean`.

* **EXIT 0**, no errors, no warnings, no `sorry` in the file.
* `#print axioms` results:
  * `normalizedLogVolume_smul_canonicalUnitReference`: `[propext, Classical.choice, Quot.sound]`;
  * `normalizedLogVolume_smul_pow`: `[propext, Classical.choice, Quot.sound]`;
  * `normalizedLogVolume_secondDifference_zero`: `[propext, Classical.choice, Quot.sound]`;
  * `no_mu2l_sqrt_neg_one`: `[propext, Quot.sound]`;
  * `padic_no_sqrt_prime`: `[propext, Classical.choice, Quot.sound]`.
* The determinant identity and its two corollaries carry `[Measure.Regular μ]` (regular additive Haar); the affine/MA-vanishing and no-go sections do not need it.
* `statement_compiles = yes` and `proof_body_checked = yes` for this file; `kernel_closed = no` (the file is not part of a closed target chain and no comparator was run); `target_accepted = no`.

Not run: full project `lake build`, integration into `PaperXiFSourceLink`/`StepXIContract`, comparator acceptance, transitive axiom audit of the whole chain. The file is new and does not modify any existing file; it should be registered in the ledger by the integrator.

## 7. What would change the verdict

1. A construction of a quaternion-division-algebra module structure on the hull carrier *from actual source data* (not posited).
2. A theorem identifying a non-archimedean MA measure with the procession-normalized Haar log (a new comparison theorem, not available in S728).
3. The normalization identity `c_norm = order` (equivalently `qVFamNormRatio = 1` in the S121 formula), which is arithmetic and independent of any determinant.

None of these is present. Do not replace the target by a determinant equation, do not replace the root unit by a quaternionic Gram matrix, and do not weaken the exact hull equality to a volume comparison.

**Concrete next executable steps.** (i) If the determinant route is to be used at all, the only missing arithmetic input is `c_norm = order` (equivalently `qVFamNormRatio = 1`); attempt that as a separate normalization task, not as a volume computation. (ii) Otherwise keep S822 as the determinant restatement of the already-exact S799/S801/S812 hull log; it adds no new gap consumer. (iii) A quaternionic construction should not be attempted until an actual source-induced `D`-module structure on the hull carrier exists.

## 8. Not run / caveats

* The compile status is the one recorded in §6; I did not run a full `lake build` of the project, and I did not modify any existing file.
* The "p-adic MA" terminology in this memo refers to the second difference of the log-volume on the coefficient lattice (the only object available); it is not a claim about Berkovich MA, which has no comparison theorem here.
* The quaternionic no-go is about the current objects/carriers. It is not a claim that no p-adic quaternionic linear algebra exists; Dieudonné determinants/reduced norms exist, but are scalar for the Haar modulus.
* S817's `c_norm` is `QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient` (the spectral normalized coefficient), not the separate order-coefficient of `QVFamNormalizedCoefficientActual`; the two namespaces must not be conflated.
* **Build-risk note (not acted on).** In the current Mathlib olean, `MeasureTheory.distribHaarChar_mul` carries a `[Regular μ]` hypothesis; S822 states it explicitly. The pre-existing core file `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean` calls `distribHaarChar_mul` / `distribHaarChar_eq_of_measure_smul_eq_mul` in its source without such a hypothesis, and its olean predates the current interface. S822 compiles against the oleans; if that core file is ever rebuilt from source, it may need the regularity hypothesis added. I did not modify it.
