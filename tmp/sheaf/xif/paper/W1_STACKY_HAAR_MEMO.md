# W1 memo: stacky Haar log-volume on the finite L(mu_2l) root stack

Date: 2026-10-30
Status: research memo + compiled Lean; no fake carrier, no surrogate target, no change of
target.  Companion kernel: `tmp/sheaf/xif/paper/S824RootStackyHaarVolumeActual.lean`
(`lake env lean`, EXIT=0; all main declarations have axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

Related files: `S782FiniteRootStackExtensionActual.lean` (finite L(mu_2l) root stack),
`S709RootImageRadiusFormulaActual.lean` (actual root norm), `S793PaperLeastLambdaOHullActual.lean`
(least lambda*O hull = fractional-lattice region at `order/(2l)`),
`S799LeastLambdaOPaperTargetActual.lean` (least-hull log formula conditional on completion
scaling data), `S817StackRootUnitNormActual.lean` (actual stack-root norm vs paper norm),
`S822PadicDetHullActual.lean` (p-adic determinant on the tensor block, Task W5),
`S769StackyLogVolumeNormalizationActual.lean` (abstract fundamental-domain version),
`TASK_F_EQUIVARIANT_ORBIFOLD_MEMO.md`.

## 0. Executive verdict (中文摘要)

1. Task F 只把 orbifold/action-groupoid 路线接受为"1/(2l) normalization"，且当时只是
   抽象的 fundamental-domain 测度恒等式；对 paper 载体没有任何实际测度定理。
   本包把这一层升级为 **S782 有限根栈 L(mu_2l) 上的实际 Haar 测度定理**：
   - `stackMuUnit^(2l)=1`，故其 distributive Haar character = 1；
   - 因此 `rootStackHaar` 在 mu_2l 乘法作用下不变（quotient measure 的实际前提）；
   - 对实际 root/q section，**实际 Haar log-volume 满足**
     `log V(root ball) = (1/(2l)) * log V(q ball)`；
   - root ball 的 log-volume 与所选取的 2l-th root 无关（branch independence）。
   这些都不需要 completion root，也不需要 character-norm 比较。

2. **"least lambda-O hull 的 log = stacky volume" 并非无条件恒等式。** S793 的最优 hull
   是 completion tensor block 中系数 `order/(2l)` 的 spectral norm ball；S709 给出实际根
   stack unit 的谱范数是 `p^(-c_norm/(2l))`，其中 `c_norm = qVFamNormalizedCoefficient`
   是 *spectral normalized* 系数，而 paper 系数是 valuation order。S824 在
   `StackCharacterNormComparison n`（Haar determinant = 谱范数的 n 次幂，当前树中没有的
   唯一解析输入）之下证明：
   `(1/n) log dHC(root) = -c_norm/(2l) * log p`
   而 S799（在 completion scaling data D 下）给出 least hull log `= -order/(2l) * log p`。
   因此
   **[least hull log = degree-normalized stacky log]  <=>  c_norm = order**
   是 kernel-checked 的 dichotomy；若 `c_norm != order`，二者数值上不相等。

3. 所以本包的结论是 **部分正结果 + 精确 no-go**，不是闭环：
   - 正结果：1/(2l) normalization 是有限根栈上的实际测度定理；q[2u] log 关系无条件成立；
     branch independence 无条件成立。
   - no-go：不能用 stacky measure 无条件替换 paper least hull log；剩余障碍被精确定位为
     (i) `StackCharacterNormComparison`（Haar determinant/norm 桥），
     (ii) S736 的 `c_norm = order`（谱范数系数 vs valuation order），
     (iii) least hull 自身的 completion scaling data D（S799）。
   没有 fake，没有 surrogate，没有换 target；least hull 仍是 S793 的集合。

## 1. The paper object and the previous Task F state

* q[1u] = q_v, q[2u] = q_v^(1/2l); paper theta at label j is q[2u]^(j^2).
* Paper root coefficient: `qVFamPaperRootCoefficient T b = order(qVFamily)/(2l)`,
  `paperRootCoefficientFamily T b = fun _ => qVFamPaperRootCoefficient`
  (QVFamRootFactorCorrectionActual / BadPlacePaperRootThetaHullActual).
* S793: the literal least lambda*O hull (intersection of all candidate lambda*O regions
  containing the nonzero-label image) is exactly
  `paperLambdaORegion T b (paperRootCoefficientFamily T b)`
  = `arithmeticTupleFractionalLattice cRoot * arithmeticTupleHolomorphicLattice`.
  No closure; the old union/closure hull is only a superset.
* S799: `paperLeastLambdaOHullLog = -((sum cRoot) * log p)` conditional on
  `ArithmeticTuplePureFractionalScalingData` at cRoot (a completion generator of norm
  `p^(-cRoot)`).  That datum is the recorded completion-scalar gap; S342/S719 say the
  analogous completion 2l-th root is impossible, and the scaling data at a non-integral
  value-group exponent is at least not available.
* Task F: accepted the orbifold/action-groupoid route only for the "1/(2l) normalization",
  via the abstract `IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self` identity;
  explicitly did NOT construct the paper hull log or identify the stacky volume.

## 2. New actual measure layer (S824, EXIT=0)

File: `tmp/sheaf/xif/paper/S824RootStackyHaarVolumeActual.lean`.

### 2.1 Finite-order character and Haar invariance

* `stackMuUnit_pow_twoL : stackMuUnit^(2*l.value) = 1`.
  Proof: the unit is the subfield image of the ambient primitive root `stackMuRoot`;
  `stackMuRoot_pow` gives the ambient equation, and the subfield coercion is injective.
* `nnreal_pow_eq_one : 0 < n -> x^n = 1 -> x = 1` for `x : NNReal` (positive real).
* `distribHaarChar_finiteOrder_eq_one`: if `u^n = 1`, then
  `distribHaarChar L u = 1`.  This uses only that `distribHaarChar` is a monoid
  homomorphism into `NNReal`: `dHC(u)^n = dHC(u^n) = dHC(1) = 1`, and a positive
  real with a positive power equal to 1 is 1.  No determinant, no norm comparison,
  no fundamental domain.
* `distribHaarChar_stackMuUnit_eq_one`: specialization to `stackMuUnit`.
* `rootStackHaar_smul_stackMuUnit (S)`:
  `rootStackHaar (stackMuUnit • S) = rootStackHaar S` for every set S.
  Proof: Mathlib `MeasureTheory.distribHaarChar_mul` gives
  `dHC * mu S = mu (u • S)`; with dHC = 1 this is the claim.  The required
  instances are supplied explicitly:
  `Measure.isAddHaarMeasure_addHaarMeasure` and `Measure.regular_addHaarMeasure`
  (the typeclass search does not find these automatically for `Measure.addHaar`).
  This is the actual quotient-measure prerequisite on the *actual* finite root stack.

### 2.2 Stacky log-volume of a dilated unit ball

* `stackUnitBall = closedBall 0 1` in L.
* `unitBall_pos`, `unitBall_fin`: positive finite Haar mass (uses
  `Measure.measure_pos_of_nonempty_interior` and compactness of the closed ball in
  the proper space L).
* `closedBall_smul_unit_eq (u)`: `u • stackUnitBall = closedBall 0 ||u||`.
  Proof: multiplication by a field unit is an additive isometry; the image of the unit
  ball is exactly the ball of radius `||u||`, and the inverse unit gives the converse.
* `stackyLogVolume mu S = log (mu S).toReal - log (mu stackUnitBall).toReal`
  (unweighted local log-volume relative to the integral structure).
* `stackyLogVolume_closedBall_unit`:
  `stackyLogVolume mu (closedBall 0 ||u||) = log (dHC L u)`.
  This is the exact Haar/determinant identity on the finite root stack, for an arbitrary
  additive Haar `mu` (with `Regular`).  It is the L-analogue of the tensor-block
  determinant theorem `normalizedLogVolume_smul_canonicalUnitReference` in
  S822PadicDetHullActual (Task W5); here it is proved for the actual finite root stack,
  not for the completion tensor block.

### 2.3 The q[2u] normalization (unconditional)

* `stackRootUnit = (stackRootSection).1`, `stackQUnit = (stackQSection).1`;
  `stackRootUnit_pow : stackRootUnit^(2l) = stackQUnit` (from S782's
  `stackRootSection_pow`).
* `stackyLogVolume_root_eq_inv_card_mul_q`:
  `stackyLogVolume mu (closedBall 0 ||stackRootUnit||)
     = (1/(2l)) * stackyLogVolume mu (closedBall 0 ||stackQUnit||)`.
  Proof: both sides are logs of dHC (2.2); dHC(root)^(2l) = dHC(q) because dHC is a
  monoid hom and root^(2l)=q; take logs and divide by 2l (with `log(dHC) > ...`).
  This is the **actual Haar-measure version of q[2u] = q[1u]^(1/2l)** on the finite root
  stack.  It does not need a completion root and does not need the character-norm
  comparison: the identity is at the level of the actual additive Haar on L.

### 2.4 Branch independence (unconditional)

* `stackyLogVolume_branch_independent`: for any unit `zeta` with `||zeta||=1` (in
  particular any `mu_2l` element, by `norm_eq_one_of_pow_eq_one` or the finite-order
  argument), the closed balls of radii `||zeta * root||` and `||root||` coincide, so
  the log-volumes coincide.  (The equality of the balls is literal because
  `||zeta * root|| = ||zeta|| * ||root|| = ||root||`; the corresponding multiplicative
  branch independence also follows from `dHC(zeta)=1` for the *scaled* balls, which is
  the same computation as 2.1.)
  This is the only property the paper actually needs from the mu_2l ambiguity: the
  branch-independent log-volume of the theta value.

## 3. Relation to the least lambda*O hull: the exact dichotomy

### 3.1 The actual root norm

* `stackRootUnit_norm_eq`: the norm of the stack root unit equals
  `rootNormedElementNorm T b` (definitional, unfolding the S782/S759 constructions).
* `stackRootUnit_norm_eq_p_rpow`:
  `||stackRootUnit|| = p^(-c_norm/(2l))`, where
  `c_norm = qVFamNormalizedCoefficient T b = -logb_p ||qVFamily.q||_normalized`
  (S709 + QVFamNormalizedGeneratorSupplyActual).
  This is the actual spectral norm of the root in L(mu_2l).

### 3.2 The character/norm comparison and the dichotomy

* `StackCharacterNormComparison n`:
  `forall u : L^*, log (dHC L u) = n * log ||u||`.
  For the finite extension `L/Q_p` the natural `n` is `[L : Q_p]`; indeed the Haar
  determinant of `x |-> u*x` is the field norm `N_{L/Q_p}(u)`, whose p-adic absolute
  value is `||u||^[L:Q_p]` for the spectral norm.  This is a true theorem of local
  field theory, but it is **not** in Mathlib/the current tree, and it is not proved by
  S824.  It is recorded as a named exact Prop, not assumed.
* Under `StackCharacterNormComparison n` (n > 0),
  `stackyDegreeNormalizedLog_root_eq`:
  `(1/n) * log (dHC(root)) = -(c_norm/(2l)) * log p`.
  Proof: the comparison plus `||root|| = p^(-c_norm/(2l))` and `Real.log_rpow`.
* Under the same comparison and S799's completion scaling data D,
  `stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order`:
  `(1/n) * log (dHC(root)) = paperLeastLambdaOHullLog
     <=> c_norm = qVFamily.order`.
  This is a kernel-checked equivalence, not an assertion of either side.
* Contrapositive:
  `stackyLog_ne_paperLeastHullLog_of_cnorm_ne_order`: if
  `c_norm != order`, the two scalars differ.

### 3.3 Why `c_norm = order` is not available

`qVFamNormalizedCoefficient` is `-logb_p` of the **spectral normalized** norm of
`qVFamily.q`; `qVFamily.order` is the **valuation exponent** of the same q
(`FinitePlaceQCandidate.order = Int.toNat(-toAdd(unzero(v q)))`, S795).
In the normalized completion of a p-adic field, the spectral norm has value group
`p^(-(1/e_K) Z)` (the extension of the Q_p norm), so
`c_norm = order / e_K` with `e_K` the ramification index of the completion.
Therefore `c_norm = order` holds only in special cases (e.g. `e_K = 1` or a
norm-instance coincidence), and is exactly the S736 norm-instance gap.  S817 records
the same obstruction from the stack side (`stackRootNormExponentDifference =
(c_norm - order)/(2l)`).  No new arithmetic input in this package proves it.

## 4. Explicit no-go statements

* **N1 (numerical no-go).**  There is no unconditional theorem
  `leastHullLog = stackyVolume`.  Under the character/norm comparison and S799 data,
  the identity is *equivalent* to `c_norm = order`; if this fails, the two numbers differ
  (S824, kernel-checked).
* **N2 (coefficient no-go).**  The paper least hull is the spectral ball at
  `order/(2l)`; the actual root ball in L(mu_2l) is the ball at `c_norm/(2l)`.  They are
  the same ball only when `c_norm = order`.  The stacky measure computes the latter, not
  the former.
* **N3 (carrier no-go, not formalized).**  The least hull is a subset of the completion
  tensor block `qVFamTensorBlock T b`; the stacky measure lives on
  `rootStackExtension T b`.  There is no canonical measure-preserving transport between
  them: the root is not in the completion (S342: a completion 2l-th root would force
  `2l | order`, contradicting `Nat.Coprime order l`), so no K-algebra map L -> K
  sending the root to a completion point exists.  The comparison in S824 is therefore a
  comparison of normalized log *scalars*, not a pushforward of the stacky measure to the
  hull.  Any future "identification" must produce this transport or a new
  mono-analytic/log-volume argument; it cannot be read off from the quotient measure.
* **N4 (Task F phrasing correction).**  The mu_2l quotient measure of an invariant set is
  `mu t / (2l)`; its log is `log mu t - log(2l)` (a constant shift), **not** the
  multiplicative `1/(2l)` factor on the divisor/log value.  The paper's `1/(2l)`
  coefficient is the *log-divisor* relation between the root line and the q-line
  (`log q = 2l log r`), which S824 proves as the actual Haar identity in 2.3.  Both
  statements are true but they are different operations; conflating them was the main
  imprecision of the Task F memo.  Only the log-divisor relation matches
  `-order/(2l) * log p`.

## 5. What the stacky route does buy (positive)

1. The 1/(2l) normalization is now a theorem about the **actual** additive Haar of the
   **actual** finite root stack L(mu_2l), not an abstract fundamental-domain convention.
2. The mu_2l invariance of the measure is proved by a finite-order character argument
   that is independent of the deeper determinant/norm comparison.  This is the
   measure-theoretic content of "Theta value determined up to mu_2l": the log-volume is
   mu_2l-invariant.
3. The q[2u] log identity is unconditional and does not use a completion root.  It
   therefore survives the S342 impossibility of a completion root; it is the correct
   home of the paper's fractional root normalization.
4. The remaining gap is reduced to two named analytic/arithmetic statements:
   `StackCharacterNormComparison` and `c_norm = order` (plus the completion scaling
   data D for measuring the least hull itself).  No ambiguity remains about what the
   stacky measure computes.

## 6. What would close (or definitively refute) the identification

* (C1) Prove `StackCharacterNormComparison ([L:Q_p])` for the finite root stack.
  Route: the spectral norm satisfies
  `spectralNorm^[L:Q_p] = |N_{L/Q_p}|` (Mathlib's
  `spectralNorm_pow_natDegree_eq_prod_roots` / `spectralNorm_eq_norm_coeff_zero_rpow`
  are the available tools); the Haar scaling of multiplication by a uniformizer is the
  index of the maximal ideal, and the residue-cardinality computation gives the same
  power.  The repo already has the prime-scalar case
  (`real_log_distribHaarChar_arithmeticTuplePrimeScalarUnit_zpow`,
  `measure_prime_smul_finiteDimensional`); the missing step is the general unit
  decomposition `u = pi^k * v` in L.
* (C2) Prove `c_norm = order` (S736) or accept that the paper coefficient should be
  `c_norm`.  The latter is a target change and is not done here.
* (C3) Either construct the completion scaling data D at `order/(2l)` (S799) or compute
  the raw completion Haar log of the least hull directly via the value group
  (the ball at a non-integral exponent is the ball at its ceiling in `(1/e_K)Z`; this
  gives the raw log, not the paper fractional log, and is a separate no-go worth
  formalizing).
* (C4) If one wants an actual pushforward of the stacky measure to the hull, construct a
  mono-analytic/log-volume transport; the carrier obstruction N3 shows that an algebraic
  transport is impossible.

## 7. Lean inventory (S824, EXIT=0)

Declarations:
`stackMuElem`, `stackMuElem_pow`, `stackMuUnit_pow_twoL`, `nnreal_pow_eq_one`,
`distribHaarChar_finiteOrder_eq_one`, `distribHaarChar_stackMuUnit_eq_one`,
`rootStackHaar_smul_stackMuUnit`, `stackUnitBall`, `stackyLogVolume`,
`stackyLogVolume_unitBall`, `unitBall_pos`, `unitBall_fin`,
`closedBall_smul_unit_eq`, `stackyLogVolume_closedBall_unit`, `stackRootUnit`,
`stackQUnit`, `stackRootUnit_pow`, `stackyLogVolume_root_eq_inv_card_mul_q`,
`stackyLogVolume_branch_independent`, `stackRootUnit_norm_eq`,
`stackRootUnit_norm_eq_p_rpow`, `StackCharacterNormComparison`,
`stackyDegreeNormalizedLog_root_eq`,
`stackyLog_eq_paperLeastHullLog_iff_cnorm_eq_order`,
`stackyLog_ne_paperLeastHullLog_of_cnorm_ne_order`.

Axiom audit (`#print axioms` at the end of the file):
all eight audited main declarations report only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

No target change, no surrogate, no fake carrier.
