# W3 memo: μ_{2l} trace / Jones index on the finite root stack

Date: 2026-10-30. Task W3 (upgrade Task H's "paper log is already a trace,
1/(2l) is the Jones index" from prose to a tool). Status: compiled Lean
construction + exact no-go/criterion, not a proof of Cor 3.12.

Files:

* Lean: tmp/sheaf/xif/paper/W3RootStackTraceIndexActual.lean
* Axiom audit: tmp/sheaf/xif/paper/_W3_axiom_audit.lean
  (compiled against the built olean; output in
  tmp/sheaf/xif/paper/logs/W3_axiom_audit_final.log)
* This memo.

## 0. Verdict (Chinese summary)

1. **构造成功（在归一化层面）**：在 S782 的有限 root-stack 载体和 S793 的
   least λO hull 上，μ_{2l} 的 regular representation 的 trace character
   被实际计算：Tr(1) = 2l，Tr(g) = 0 (g ≠ 1)；归一化 trace τ = Tr/(2l)
   满足 τ(1) = 1。Jones index 取 2l，1/(2l) 是其倒数归一化。
   Lean 中这是 'matrixTrace_regularPerm' / 'traceCharacter_eq_delta' /
   'jonesIndex' / 'jonesNormalization'。

2. **S782 的 root section 正是 trace 归一化**：qSection 的 divisor 坐标是
   order(q)；rootSection 的 divisor 坐标是 order(q)/(2l)；且
   rootSection^(2l) = qSection。把 q divisor 放在 μ_{2l} 的一个 fundamental
   domain 上，则 q divisor = Tr(f_q)，root divisor = τ(f_q)。这是
   'stackRootSection_toAdd_eq_normalizedTrace_qOrder' /
   'stackQSection_toAdd_eq_trace_qOrder'。

3. **S793 least hull 的 scaling 就是 root divisor**：S793 证明 least λO
   hull = 系数为 paperRootCoefficientFamily = order(q)/(2l) 的 λO region。
   这个系数逐字等于 S782 rootSection 的 divisor。因此 least hull 的
   scaling 是 q scaling 的 τ-归一化：
   'paperLeastLambdaOHull_eq_lambdaO_rootSection' /
   'paperLeastHullScaling_eq_normalizedTrace_qOrder'。

4. **系数层面的 qPilot/hull 比较成立**：在每 b 的单因子模型里，paper q
   coefficient log-volume 是 -order(q) log p，least hull coefficient
   log-volume 是 -(order(q)/(2l)) log p；后者是前者的 (1/(2l)) 倍，且因为
   q log-volume ≤ 0，得到 q ≤ hull。Lean：
   'paperLeastHullCoefficientLogVolume_eq_normalizedTrace_qLogVolume' /
   'paperQLogVolume_le_paperLeastHullLogVolume'。这里比较的是 paper
   coefficient 的 log-volume，不是实际 qPilot 的 normalized spectral log，
   也不是全局加权 Cor 3.12。

5. **No-go / 精确判据**：把 least hull 系数直接等同于 1/(2l) 只在
   q.order = 1 时成立；q.order > 1 时严格大于 1/(2l)。
   'leastHullCoefficient_eq_jonesNormalization_iff' /
   'jonesNormalization_lt_leastHullCoefficient_of_one_lt_order'。
   所以 trace/index 是 hull scaling 的**分母归一化**，不是 hull log 本身；
   把它当成 log 或当成 hull region 的构造是范畴错误（与 S732 的 O1/O2/O4
   一致）。

6. **未完成的对象级桥**：paper least hull log 的实际测度（在 completion
   或正确 carrier 上）与 S782 finite-L root-stack Haar 仍未识别。S809 已把
   它精确写成 'StackRootUnitNormBridge' + 'StackHaarNormalizationBridge'；
   W3 的 trace/index 不填这两个桥。实际 qPilot 的 normalized log 还带有
   residue degree / norm-instance correction（'QVFamNormalizedCoefficient'
   与 'qVFamPureCoefficient' 的 exact gap），也不是 trace/index 能替代的。

**没有 fake、没有 surrogate、没有换 target。** W3 的新工具是：把 1/(2l)
从一个解释性常数升级为在 S782/S793 实际对象上可核对的 trace/index 归一化
字典；它减少的是“1/(2l) 为何是 Jones 归一化”的缺口，不减少 paper
least hull log 与 root-stack Haar 之间的对象级缺口。

## 1. Paper anchors

* IUT III, Remark 3.9.4 (i): log-volume is log of the integral over an ample
  measure space; additive translates have equal log-volume. Thus the paper's
  log-volume is already log∘Haar, i.e. the commutative trace picture.
* IUT III, Remark 3.9.5 (i): the holomorphic hull of a relatively compact
  region is the smallest λ·O containing it, and its log-volume is log|λ|.
* IUT III, Proposition 3.9 (i): normalization μ^log(O) = 0 and multiplication
  by e adds 1.
* IUT III, Definition 3.8 (i): the Θ- and q-pilots are objects of realified
  Frobenioids, determined by generators up to torsion. The μ_{2l} ambiguity
  lives in the possible images/Kummer isomorphisms, not in the object. So a
  trace can normalize the finite root fiber, but cannot by itself build or
  identify the hull region (S732 O1/O4).
* IUT III, Corollary 3.12: the Θ side is subject to (Ind1)(Ind2)(Ind3), the q
  side is not. A single trace/Hilbert space is a common container, which the
  paper architecture avoids (S732 O5). W3 therefore uses trace/index only as
  a finite-fiber normalization, never as a common container for the two
  pilots.

## 2. The trace/index dictionary (constructed)

### 2.1 The finite group and its regular representation

Let n = 2l (S782's μ_{2l}). Model the finite group as ZMod n. The regular
representation on ℝ^n has permutation matrices P(a), (P(a) f)(x) = f(x - a).
The trace character is

  Tr(P(0)) = n,   Tr(P(a)) = 0 for a ≠ 0,

because a translation of ZMod n has n fixed points at a = 0 and none
otherwise. The normalized trace is τ(f) = (1/n) Σ_a f(a); in particular
τ(1) = 1. The finite-group Jones index of the fixed-point inclusion is n;
1/n is the reciprocal index, i.e. the Plancherel/trace normalization of the
regular representation.

Lean (W3RootStackTraceIndexActual):

* 'rootStackIndex l = 2 * l.value';
* 'stackFiberTrace', 'stackFiberNormalizedTrace';
* 'stackFiberTrace_one : Tr(1) = 2l', 'stackFiberNormalizedTrace_one : τ(1) = 1';
* 'regularPerm', 'fixedPoints_regularPerm', 'matrixTrace_regularPerm',
  'traceCharacter_eq_delta';
* 'jonesIndex l = rootStackIndex l', 'jonesIndex_eq_two_mul',
  'jonesIndex_eq_trace_one : jonesIndex = Tr(1)',
  'jonesNormalization l = 1/(2l)', 'jonesNormalization_eq_inv_trace_one',
  'jonesNormalization_eq_inv_index'.

The statement is finite-dimensional and fully kernel-checked. The standard
subfactor/Jones-index theorem for a free finite group action is cited, not
formalized; what is formalized is exactly the finite trace character and the
identification of its normalization with 1/(2l).

### 2.2 S782: q divisor, root divisor, and the fundamental domain

S782 defines

  stackQSection    = (stackLUnitMap (rootNormedUnit^(2l)), ofAdd (order(q))),
  stackRootSection = (stackLUnitMap (rootNormedUnit), ofAdd (order(q)/(2l))),

and proves stackRootSection^(2l) = stackQSection.

Take the fundamental-domain function

  f_q(a) = order(q) if a = 0, else 0.

Then

  Tr(f_q) = order(q)                (= qSection divisor),
  τ(f_q)  = order(q)/(2l)           (= rootSection divisor).

So the root section's divisor is literally the normalized trace of the q
divisor concentrated on one fundamental domain; the q section is the
unnormalized trace. The section power relation is the same statement at the
level of the coefficient: q coefficient = (2l) · root coefficient.

Lean:

* 'stackQSection_toAdd', 'stackRootSection_toAdd';
* 'fundamentalQFunction', 'stackFiberTrace_fundamentalQ',
  'stackFiberNormalizedTrace_fundamentalQ';
* 'stackRootSection_toAdd_eq_normalizedTrace_qOrder',
  'stackQSection_toAdd_eq_trace_qOrder';
* 'stackRootSection_pow_index',
  'qCoefficient_eq_index_mul_rootCoefficient';
* 'stackMuUnit_pow_index' (the actual S782 primitive μ_{2l} unit has
  index-th power one, so the action factors through ZMod (2l));
* 'stackMuAction_divisor' (the action fixes the divisor coordinate).

The last two are small but important for faithfulness: the finite-fiber trace
is not an unrelated toy; the actual S782 action has the same index and acts
only on the unit fiber.

### 2.3 S793: the least λO hull is at the root-section divisor

S793 defines the literal least λO hull as the intersection of all candidate
λO regions containing the nonzero-label Θ image, and proves

  paperLeastLambdaOHull = paperLambdaORegion (paperRootCoefficientFamily),

with paperRootCoefficientFamily = order(q)/(2l). W3 proves that this family
is exactly the S782 root-section divisor, and hence

  paperLeastLambdaOHull
    = paperLambdaORegion (fun _ => toAdd (stackRootSection).2).

Lean:

* 'paperRootCoefficientFamily_eq_rootSection_toAdd';
* 'paperLeastLambdaOHull_eq_lambdaO_rootSection';
* 'paperLeastHullScaling_eq_normalizedTrace_qOrder'.

This is the main new cross-file bridge: the least λO hull of S793 is not just
"some coefficient order/(2l)"; it is the λO region whose scaling is the
μ_{2l}-normalized q divisor of S782.

### 2.4 The coefficient log-volume comparison

At each b, with p = qVFamTensorP b, define

  L_q    = -order(q) · log p,
  L_hull = -(order(q)/(2l)) · log p.

Then L_hull = (1/(2l)) L_q. Since L_q ≤ 0 and 0 < 1/(2l) ≤ 1, we get
L_q ≤ L_hull. This is the exact q/hull comparison at the level of the paper
coefficient formulas. The factor 1/(2l) is exactly τ(1), i.e. the reciprocal
of the trace of the identity / Jones index.

Lean:

* 'paperQCoefficientLogVolume', 'paperLeastHullCoefficientLogVolume';
* 'paperLeastHullCoefficientLogVolume_eq_normalizedTrace_qLogVolume';
* 'paperQLogVolume_le_paperLeastHullLogVolume'.

Caution: these are log-volumes of the paper **coefficient** formula
(-c·log p). They are not the normalized Haar log of the actual region on the
correct root-stack/extension carrier; that is the remaining S809 bridge. Also,
they are per-b one-factor quantities, not the global weighted/procession
Cor 3.12 scalar.

There is a separate "log of the coefficient" identity:

  -log(order(q)/(2l)) = -log(order(q)) + log(2l),

formalized as 'leastHullCoefficientLog_eq_qCoefficientLog_add_log_index'.
This shows the additive log(index) correction in the exponent. It must not be
confused with the log-volume, which is linear in the coefficient
(-c·log p). The memo records both because both are useful: the coefficient
log shows the exact index correction; the coefficient log-volume is the
paper-shaped comparison.

## 3. What is constructed, and what is not

### Constructed (actual, compiled)

1. The μ_{2l} regular-representation trace character and its normalized trace
   (Tr(1) = 2l, Tr(g) = 0, τ(1) = 1).
2. The Jones normalization dictionary: index = 2l, reciprocal index = 1/(2l).
3. The S782 root-section divisor as τ(f_q), and q-section divisor as Tr(f_q).
4. The S793 least λO hull as the λO region at the S782 root-section divisor.
5. The per-b coefficient log-volume comparison L_q ≤ L_hull with factor 1/(2l).
6. Exact no-go/criterion for the literal identification
   leastHullCoefficient = 1/(2l).

### Not constructed (still exact gaps)

1. **The paper least hull log on the correct carrier.**
   S793/S799 compute the least hull as a region and give the formula
   conditional on completion scaling data. The completion scaling datum at
   the paper coefficient order/(2l) is a completion-root obstruction
   (S342 / PAPER_THETA_NORMALIZATION_STATUS). S809 records the exact
   alternative: 'StackRootUnitNormBridge' (the stack root unit has norm
   p^(-Σ paperRootCoefficientFamily)) and 'StackHaarNormalizationBridge'
   (the finite-extension Haar log equals the paper least hull log). W3 does
   not prove either. The trace/index dictionary is compatible with both but
   does not replace them.
2. **The actual qPilot normalized log.**
   The actual q scalar uses the normalized spectral norm coefficient
   qVFamNormalizedCoefficient, while the paper coefficient is order(q)/(2l).
   The relation is controlled by the correction layer
   ('qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio',
   'BadPlaceCorrectionControlActual', 'QVFamNormalizedCoefficientGap').
   This is not a trace/index statement; W3 only accounts for the factor 2l.
3. **Global Cor 3.12.** W3 is per-b and coefficient-level. It does not
   produce the global weighted/procession-normalized paper inequality, and
   it does not touch the PaperXiFSourceLink fields.

## 4. No-go and exact criteria

### 4.1 The literal "hull coefficient = bare Jones normalization" is false

The least hull coefficient is order(q)/(2l). The bare Jones normalization is
1/(2l). They are equal iff order(q) = 1:

  leastHullCoefficient_eq_jonesNormalization_iff :
    (order(q)/(2l) = 1/(2l)) ↔ order(q) = 1.

If order(q) > 1, the hull coefficient is strictly larger
('jonesNormalization_lt_leastHullCoefficient_of_one_lt_order'). Thus the
trace/index value is the denominator of the hull scaling, not the hull
scaling itself. Any use of "least hull coefficient = bare Jones
normalization" as a numerical equality is a no-go except in the degenerate
q-order-one case. The same caution applies to any "hull log = trace/index"
slogan: the log-volume is -c log p, not log c, and the trace only supplies
the factor 1/(2l).

### 4.2 Trace/index is blind to the root data

S732's 'trace_functional_blind_to_roots' shows that any functional invariant
under n-th roots of unity cannot distinguish the n roots. The μ_{2l} trace
here is exactly such an invariant (it is the regular-representation trace,
averaged over the fiber). It sees the finite index and the normalized count,
not which 2l-th root/Kummer identification is used. The paper's hull is over
the possible images relative to the Kummer isomorphisms (S732 O4), so the
trace cannot construct or identify that hull. This is not a defect of the
formalization; it is a structural limitation of the trace route.

### 4.3 The paper log is log∘Haar, not a linear trace

S732 proves 'no_additive_of_scaling_and_translation': the paper scaling law
and Haar translation invariance are incompatible with additivity on disjoint
regions. Hence the paper log-volume cannot be a linear trace/index
functional; the only faithful trace picture is log of the Haar measure
(Remark 3.9.4 (i)), which is already the paper's own definition. W3 confirms
this at the finite-fiber level: the trace normalizes the fiber, while the
log-volume is the logarithm of the Haar measure on the region.

### 4.4 No common container

A single trace/Hilbert space containing both pilots is a common container.
Cor 3.12 is asymmetric: the Θ side is subject to (Ind1)(Ind2)(Ind3), the q
side is not. Producing a common container would be strictly stronger than
the paper and is not available. W3 avoids this: it uses a trace only on the
finite μ_{2l} fiber, not on a common carrier for q and Θ.

## 5. Relation to sibling files (important for integration)

At the time of writing, several sibling files in the same folder address
adjacent layers:

* S809PaperLeastHullRootStackBridgeActual: the exact root-stack norm/Haar
  bridges ('StackRootUnitNormBridge', 'StackHaarNormalizationBridge') for
  the paper least hull log. This is the correct place to continue the
  object-level gap; W3 does not fill it.
* S811StackMuPermActionActual: the full μ_{2l} permutation action on the
  finite root-stack carrier and the MulAut gap. W3's finite-fiber trace is
  the representation-theoretic shadow of that action.
* S816StackyHullInterfaceActual: a "stacky volume" (1/(2l))·card·hullLog.
  Its 'hullLogEqStacky_actual' is algebraically automatic because
  card(μ_{2l}) = 2l; it normalizes hullLog by itself and therefore is not a
  bridge from the paper hull log to the root-stack Haar. Do not treat S816's
  'HullLogEqStacky' as the missing object-level bridge. W3's content is
  different: the trace character, the S782 divisor identity, and the
  S793/S782 scaling identification.
* S812/S799: the least-hull log formula conditional on completion scaling
  data; the completion-root obstruction remains.

## 6. Next executable steps

1. **Fill the S809 norm bridge.** Show the S782 stack root unit has norm
   p^(-Σ paperRootCoefficientFamily). This is an extension-field norm
   computation; the exponent is exactly W3's τ(f_q), so W3 supplies the
   bookkeeping but not the norm identity.
2. **Fill the S809 Haar bridge.** Identify the finite-extension root-stack
   Haar log of the appropriate ball with 'paperLeastLambdaOHullLog'. This is
   an object-level measure transport, not a trace statement.
3. **Keep the qPilot correction separate.** Do not replace
   qVFamNormalizedCoefficient by order(q) under the trace/index banner; the
   correction layer is independent.
4. **No new trace proposal without the kill tests.** Any future trace/index
   proposal must answer: (a) does it see the 2l-root/Kummer data? (b) does it
   construct or identify the hull region? (c) does it identify the extension
   Haar? If no, it is at most the finite-fiber normalization, which W3 has
   already formalized.

## 7. Lean artifact, compile status, axioms

File: tmp/sheaf/xif/paper/W3RootStackTraceIndexActual.lean

Compile:

  lake env lean tmp/sheaf/xif/paper/W3RootStackTraceIndexActual.lean

Result: exit 0, no errors, no warnings (log:
tmp/sheaf/xif/paper/logs/W3_final_check.log, which is empty; earlier
W3_compile_final.log is empty as well).

Axiom audit: tmp/sheaf/xif/paper/_W3_axiom_audit.lean, compiled against the
built olean. Audited declarations:

* stackFiberNormalizedTrace_one
* matrixTrace_regularPerm
* traceCharacter_eq_delta
* stackRootSection_toAdd_eq_normalizedTrace_qOrder
* paperLeastLambdaOHull_eq_lambdaO_rootSection
* paperLeastHullScaling_eq_normalizedTrace_qOrder
* paperQLogVolume_le_paperLeastHullLogVolume
* leastHullCoefficient_eq_jonesNormalization_iff

All depend only on propext, Classical.choice, Quot.sound.

No sorry, no axiom, no True/PUnit, no fake data. All definitions are on the
actual S782/S793 objects (qVFamily, stackRootSection, stackQSection,
paperLeastLambdaOHull, paperRootCoefficientFamily).

## 8. Bottom line

W3 constructs the trace/index normalization tool that Task H only described:
on the actual finite root stack, 1/(2l) is the reciprocal of the
regular-representation trace of the identity / Jones index, the S782 root
section is the normalized trace of the q divisor, and the S793 least λO hull
sits exactly at that root-section divisor. The per-b coefficient log-volume
comparison follows with the factor 1/(2l).

It does not prove the paper Cor 3.12 inequality, does not identify the paper
least hull log with the root-stack Haar log, and does not identify the actual
qPilot normalized log with the paper coefficient log. Those remain the exact
object-level bridges (S809) and the correction layer, respectively. The
no-go/criterion shows that treating trace/index as the hull log itself is
false except in the q-order-one degenerate case.
