# S814 (Task W2): non-Archimedean skeleton / Tate period vs the least lambda-O paper hull

Date: 2026-10-30
Status: research memo + actual Lean file
(tmp/sheaf/xif/paper/S814SkeletonQuantizedLeastHullActual.lean).
Target unchanged; no fake/surrogate object, no new hypothesis smuggled into the
paper statement.

## 0. Verdict (Chinese summary)

结论（相对 Task I 的升级）：skeleton length 不再是"只辅助"。

1. **精确计算成立，但必须用值群（value group）形式**：least lambda-O hull
   在局部因子中就是范数球 F(c) = {x | ||x|| <= p^(-c)}；它的 normalized Haar
   log 等于 **值群骨架段 [0, c] 的加性 p-log 长度取负**，即 -Σ c'_i log p，
   其中 c' 是"实现同一球"的指数（值群 ceiling）。若 c 本身在值群中（例如
   actual root 的指数），ceiling 就是 c，得到 -Σ c_i log p。
2. **qPilot = skeleton length 的到 hull 的比较成立且无条件**：q-pilot 的
   Tate 周期长度是 ord * log p（Tate 曲线骨架 R / ord Z 的长度），对应球
   F(ord)；而 F(ord) 包含在 least hull F(ord/(2l)) 中，故
   qPilotLog <= paperLeastLambdaOHullLog 在 Lean 中**无 scaling-data 假设**地
   证明（S814）。这正是 paper 的 -|log q| <= -|log Theta| 在 least-hull
   载体上的形式（q 取 classical q_v 系数 ord）。
   由此可**无条件**推出 S799 的 paper-order 比较
   paperQPilotLogLeast = -(ord/(2l)) log p <= hull log（S799 原来需要
   scaling data），即 S814PaperHullLogInterfaceActual 的精确比较义务
   PaperHullLogComparisonRequired 可被直接满足、data 参数可去掉。
   注意：这条推论（corollary）未包含在已验证的 Lean 文件中；它在 03:40 的
   编译尝试被机器内存/库读取故障阻塞，交付给集成者补编。已验证文件与绿色
   构建逐字节一致。
3. **naive 系数公式 -Σ c_root log p 在值群未实现时是假的**：S814 证明若存在
   严格更大的 c' 给出同一球并带精确生成元，则 hull log 严格小于 naive 值。
   所以 "用 skeleton/tropical volume 精确计算" 的正确结论是值群 ceiling 公式，
   不是系数公式本身。具体反例：在 Q_p 中 F(1/2) = F(1) = pZ_p，球 1/2 的
   normalized log 是 -log p 而不是 -(1/2) log p（手算，未形式化）。
4. **root stack 的真实角色 = 值群扩张**：有限 root-stack 扩张
   L = K(q[2u], mu_{2l}) 中 actual 2l-th root 的
   范数实现系数（S709: p^(-c_norm/(2l))），故在 L 中 ceiling 精确、公式精确；
   在 base completion K_v 中只看到 quantized 值。即 **Kummer root stack 就是
   去掉 skeleton 量化缺陷的值群 1/(2l) 扩张**。这把 q[2u]/root-stack 与
   skeleton/tropical volume 接上了，也说明 paper 的 Theta log 必须在 L 侧
   计算（S812 的 carrier/measure transport 仍是精确缺口）。
5. **literal Berkovich/SYZ skeleton 仍是 no-go**：有限扩域的 Berkovich 空间
   是一个点，tensor block 的球没有非平凡的 Berkovich 骨架；Tate 骨架属于
   E_q，不属于 hull。能精确工作的是 "值群/热带骨架"（valuation skeleton），
   它不是 Berkovich 模型骨架，也不做测度等价的声明。

因此本任务把 Task I 的 "auxiliary only" 升级为：
*（值群/热带意义下的）精确计算 + 无条件的 qPilot 比较*；
同时保留两个 no-go：literal Berkovich carrier 和未经实现的系数公式。

## 1. What changed since Task I (S728/S729)

Task I (S728, S729) recorded:

* q-pilot log = skeleton length = ord(q) * log p (Tate period dictionary);
* Theta hull log = lattice/Haar volume; the exact hull equality
  paperRootThetaHull = F(c_paper) * O_hol was the gap;
* no paper-faithful bridge; skeleton "auxiliary only".

Three current facts change the picture:

1. **S793**: the paper Theta carrier is the *least* lambda-O hull, and it is
   *exactly* a fractional-lattice region:
   paperLeastLambdaOHull T b = F(paperRootCoefficientFamily T b) * O_hol.
   No closure/union equality is needed any more.
2. **S799/S801/S812**: given ArithmeticTuplePureFractionalScalingData at the
   paper coefficient, the least-hull log is -Σ c_root * log p (conditional
   formula).  S812 adds the finite root-stack carrier L(mu_2l) and records the
   carrier/measure transport as an explicit bridge.
3. **S782**: the finite root-stack extension L = K(root_b, mu_2l) with the sections
   stackQSection (divisor ord), stackRootSection (divisor ord/(2l)),
   stackRootSection^(2l) = stackQSection is actual.

The missing piece was the *value-group quantisation*: the ball F(c) depends only
on the value-group ceiling of c.  S814 makes this the content of the exact
computation and uses it to remove the scaling-data hypothesis from the
*comparison* (keeping it only for the *formula at the paper coefficient*).

## 2. The exact objects (repo anchors, no new objects)

### 2.1 The tensor block is a local field

qVFamTensorV = Unit and qVFamTensorTuple = (), so at each bad place b

  qVFamTensorBlock T b = ArithmeticTensorTupleBlock (qVFamTensorPlaces T b)
                          qVFamTensorTuple = CommonPrimeCompletion (place)

is the completed local field K_v (a finite extension of Q_p, p = qVFamTensorP).
O_hol = arithmeticTupleHolomorphicLattice is the integral closure O_v
(FinitePlaceNormalizedUnitScalingLogVolume.arithmeticTupleHolomorphicLattice and
arithmeticTupleCanonicalUnitReference_eq_integralClosure).

The fractional lattice is the norm ball

  arithmeticTupleFractionalLattice places tuple c
    = {x | ||x|| <= p^(-c)}          (PadicFractionalLattice.padicFractionalLattice)

and the paper regions are F(c) * O_hol.  For c >= 0 this equals F(c) itself
(the ball is an O_v-submodule), and it is compact open.

### 2.2 Least hull = norm ball (S793, actual)

  paperLeastLambdaOHull T b = paperLambdaORegion T b
      (paperRootCoefficientFamily T b)                       (S793.eq_minimal)
  paperLambdaORegion lam = F(lam) * O_hol
  paperRootCoefficientFamily T b i = ord(qVFamily T b)/(2l)

### 2.3 q-pilot = Tate skeleton length

The local q_v is an actual element of K_v (QPilotZeroLocusDivisorActual:
qVFamily, with order = exponential divisor order).  In the IUT arithmetic
normalization the paper q-pilot log-volume at b is ord * log p (IUT III,
Definition 3.8; the ledger's qPilotLogVolume), which is also the additive p-log
length of the Tate skeleton R / ord Z (Bosch-Lutkebohmert-Raynaud Ch. 9).  The
corresponding norm-ball model is F(ord); S814 shows its normalized Haar log is
exactly -ord * log p using the exact generator p^ord, so the model ball
realizes the paper q-pilot scalar as an actual Haar log.

Normalization caveat: the actual q_v in the tensor block has normalized
spectral coefficient c_norm = -logb_p ||q|| (QVFamNormalizedGeneratorSupply),
and the identification c_norm = ord is the separate object-level norm bridge
(QVFamNormalizedCoefficientOrderAudit, S734).  S814 uses the paper ord
coefficient on both sides of the inequality, so it does not depend on that
bridge; the bridge is only needed to identify F(ord) with the actual q ball.

## 3. Skeleton/tropical computation: exact form and quantisation

### 3.1 The value-group skeleton (definition)

The valuation v = -log_p ||.|| maps K_v^* onto the value group (1/e)Z (e the
ramification index over Q_p), and ||x|| = p^(-v(x)).  The ball F(c) is the
preimage of the segment [c, infinity) intersect the value group.  The additive
p-log length of the segment [0, c] is

  valueGroupSkeletonLength c = c * log p.

This is the only "skeleton" that is literally present in the paper objects.
It is *not* a Berkovich skeleton of a semistable model (see section 6).

### 3.2 Exact computation, quantised form

**Theorem (S814.paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator).**
For any exponent vector c' with

  F(c') = F(paperRootCoefficientFamily T b)      (same norm-ball lattice)

and exact local generators g_i with ||g_i|| = p^(-c'_i), the least-hull log is

  paperLeastLambdaOHullLog = - (sum_i c'_i) * log p.

This is the exact skeleton computation: the hull log is minus the skeleton
length at the realising exponent.  If c_root lies in the value group and is
realised by actual elements, c' = c_root and this specialises to the S799/S812
conditional formula.  If c_root is not in the value group, the correct c' is the
value-group ceiling ceil_v(c_root) (coordinatewise), which lies in
(c_root, c_root + 1/e]; then the hull log is -sum ceil_v(c_root) * log p.

**Theorem (S814.paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization).**
If such a c' is coordinatewise strictly larger than c_root, then

  paperLeastLambdaOHullLog < - (sum_i c_root_i) * log p.

So the naive coefficient formula is *false* without value-group realisation.
This is a Lean theorem, not just a remark.

Parallel packets S815/S819 settle the existence side of the same picture:
S815.paperScalingData_nonempty_iff_localGenerator reduces the paper scaling
data to a local generator of norm p^(-cRoot), and S819 records the exact
value-group characterization of the normalized completion norm (an explicit
hypothesis) with the conditional no-go
noLocalGenerator_of_valueGroupNoGo: if cRoot is not in (1/e)Z then no local
generator exists.  S814 is the value side of the same dichotomy: even when no
generator at cRoot exists, the hull log is still exactly computable at the
value-group ceiling c', and the naive coefficient formula has the strict
defect of the theorem above.  S814 does not need the value-group
characterization to be proved; it takes the realizing exponent and its exact
generator as data.

### 3.3 Concrete quantisation example (pen and paper, not formalised)

In K = Q_p, the value group is Z.  With c = 1/2,

  F(1/2) = {x | ||x|| <= p^(-1/2)} = {x | ||x|| <= p^(-1)} = F(1) = p Z_p,

because p-adic norms are 0 or p^(-k), k in Z.  Hence the normalized log of the
ball at 1/2 is -log p, not -(1/2) log p; the ceiling formula gives the correct
value -ceil(1/2) log p = -log p.  For the paper coefficient ord/(2l) with ord
odd (and e = 1) the same phenomenon occurs with c' = ceil(ord/(2l)).

This example is exactly the obstruction removed by passing to the finite root
extension where the root realises the coefficient.

## 4. qPilot = skeleton length to hull: the comparison

### 4.1 Unconditional comparison (the new paper-level theorem)

Define the q-pilot ball F(ord) and its log:

  paperSkeletonQPilotLog = mu_log(F(ord)) = - ord * log p
      (S814.paperSkeletonQPilotLog_eq)

and note c_root = ord/(2l) <= ord, hence F(ord) is contained in
F(c_root) * O_hol = paperLeastLambdaOHull.  Monotonicity of the normalized log
gives, with no fractional-scaling-data hypothesis,

  **paperSkeletonQPilotLog <= paperLeastLambdaOHullLog**
  (S814.paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog).

This is the skeleton-length-to-hull comparison: the Tate period length of q
dominates (the absolute value of) the least Theta-hull log.  The two inputs
are actual: the q-pilot ball log is computed from the actual q order via the
exact generator p^ord, and the hull log is the actual normalized Haar log of
the S793 least hull.

**Proposed corollary (not in the verified file; to be added and compiled by the
integrator).**  The paper-order scalar paperQPilotLogLeast = -(ord/(2l)) log p
(S799) is above the q-pilot scalar -(ord) log p, so the same comparison should
give

  paperQPilotLogLeast <= paperLeastLambdaOHullLog

*without* the scaling-data hypothesis that S799 needed.  This would discharge the
exact comparison obligation of the PaperHullLogInterface
(S814PaperHullLogInterfaceActual.PaperHullLogComparisonRequired) and make its
data argument removable.  Status: the statement is a one-line consequence of
the verified S814 comparison plus the verified scalar inequality
sum c_root <= ord (S814.paperRootCoefficientFamily_le_qPilot), but a compile of
the corollary was blocked by machine out-of-memory / library-read failures at
03:40, so it is deliberately NOT included in the verified Lean file.  The
verified file is byte-identical (SHA256
4b51fb756a11d5761b65f623d9d8121041a982b40f3dd9c27af01f119a3ce53f) to the
green build recorded below.

### 4.2 Two-sided bounds and slack

Combining with S814.paperLeastLambdaOHullLog_le_zero:

  - ord * log p <= paperLeastLambdaOHullLog <= 0.

If the paper coefficient is realised (c' = c_root), the exact value
-(ord/(2l)) log p sits at the top of the range; the gap to the q-pilot bound is
(ord - ord/(2l)) log p = ord(1 - 1/(2l)) log p, and the quantisation defect
sum(ceil_v(c_root) - c_root) log p can only decrease the hull log further.
So the paper inequality has slack at least ord(1 - 1/(2l)) log p in the
realised case; in the base completion the slack is larger.

### 4.3 The two readings and the root-stack dichotomy

There are two readings of the paper q side:

* **Reading A (q = q_v, coefficient ord).**  The target is
  -ord log p <= hull log.  S814 proves it unconditionally (4.1).  This is the
  reading of the current canonical consumer chain
  PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog.

* **Reading B (q = q[2u], coefficient ord/(2l)).**  The target is
  -ord/(2l) log p <= hull log.  Since the actual hull log is at most
  -sum ceil_v(c_root) log p, this target holds iff ceil_v(c_root) = c_root
  coordinatewise, i.e. iff the paper coefficient is realised in the value
  group.  In the finite root-stack extension L = K(q[2u], mu_2l) it is realised by the actual
  root (S709: rootImageRadius = p^(-c_norm/(2l))), so Reading B holds there;
  in the base completion it can fail by the quantisation defect.

So the skeleton analysis does not merely bound the paper quantity: it *locates*
the root-stack obstruction.  The root stack is exactly the value-group
enlargement by the 2l-division of the q valuation, which removes the ceiling.

## 5. Root stack = value-group enlargement

On the one-dimensional skeleton R / v(q)Z, the Kummer cover

  L = K(q[2u], mu_2l) -> K_v

restricts to multiplication by 2l on the skeleton coordinate: the q[2u] period
has length v(q)/(2l) = ord/(2l) * log p, which is exactly the skeleton length
of the least Theta hull F(c_root).  S782's finite root-stack sections encode
this algebraically:

  stackQSection     has divisor ord
  stackRootSection  has divisor ord/(2l)
  stackRootSection^(2l) = stackQSection                  (S782, S812)

Hence the "q[2u] root stack" and the "Theta skeleton length" are two faces of
the same value-group division: the root is the (1/2l)-length generator of the
q skeleton circle, and the least hull is the corresponding norm ball.  This is
the precise content of the Task-I dictionary that was previously only informal.

## 6. What is a no-go

1. **Literal Berkovich/SYZ skeleton as carrier: no-go.**  For a finite
   extension L of Q_p the Berkovich space M(L) is a single point, and the
   tensor block K_v is a field, so its Berkovich analytification is also a
   point.  The ball F(c) has no non-trivial Berkovich skeleton; the Tate
   skeleton R / v(q)Z belongs to the Tate curve E_q, a different space.  No
   measure-preserving map from the paper hull to a Berkovich skeleton is
   available, and the Haar measure of the ball is not the skeleton measure of
   E_q.  (This is the measure mismatch O2 of S729, now sharpened: the exact
   numerical dictionary is at the level of value-group lengths, not of
   measures on a skeleton.)

2. **Naive coefficient formula without realisation: no-go.**  Section 3.3 and
   S814.paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization.  The
   formula -sum c_root log p is only the *upper* end of the range; the actual
   base-completion hull log is the ceiling value.

3. **"Bare" base-completion exact formula: no-go.**  Without transport to the
   finite root extension (or without the value-group realisation), the exact
   paper-coefficient formula cannot be obtained from the base completion.  The
   missing datum is exactly the S812 carrier/measure bridge, not a measure
   computation.

## 7. Exact remaining bridges

0. **S815/S819 value-group packets** (parallel): S815 reduces the paper scaling
data to a local generator of norm p^(-cRoot) and records the finite-L
alternative; S819 records the value-group characterization and the conditional
no-go for a completion generator at cRoot.  These supply the existence side
that S814's quantisation theorem takes as data.
1. **S812 bridge**: a measurable carrier equivalence
   qVFamTensorBlock T b ~ rootStackExtension T b, Haar transport, hull
   transport, and the log equality on the L side.  S814's quantisation theorem
   is stated for an arbitrary realising exponent c'; applying it on the L side
   needs the transport of the ball/carrier to L and the identification of the
   actual root norm exponent with c_root (or with c_norm/(2l), per the separate
   normalisation audit below).
2. **Normalisation audit**: qVFamNormalizedCoefficient vs qVFam order
   (QVFamNormalizedCoefficientOrderAuditActual).  The paper coefficient is
   ord/(2l) (S782/S775); the spectral normalized coefficient c_norm is
   -logb_p ||q|| and equals ord only under the normalized norm/valuation
   formula.  S814 uses the paper ord coefficient, so it does not depend on
   this audit: F(ord) is the ball whose normalized Haar log is exactly the
   paper q-pilot scalar -ord log p, and the inequality only uses the paper
   scalar.  Identifying F(ord) with the ball of the actual q_v (c_norm = ord)
   and the L-side transport are the places where this audit enters.
3. **Procession normalisation**: PaperSignedHull.hull_logVolume_eq_average.
   S814 computes the ambient hull log, not the procession average.  The
   comparison of the two is the paper normalization obligation already recorded
   in S729 (O4); it is orthogonal to the skeleton computation.

## 8. Lean inventory and verification status

File: tmp/sheaf/xif/paper/S814SkeletonQuantizedLeastHullActual.lean

Definitions:
* valueGroupSkeletonLength c = c * log p (additive skeleton length);
* paperQPilotExponentFamily = constant (ord : Real) on qVFamTensorV = Unit;
* paperQPilotGenerator i = (p : K_v) ^ (ord : Int), paperQPilotGenerator_norm:
  ||paperQPilotGenerator i|| = p^(-(ord : Real));
* paperQPilotScalingData : ArithmeticTuplePureFractionalScalingData at ord
  (from arithmeticTuplePureFractionalScalingData_ofGenerator);
* paperSkeletonQPilotRegion = paperLambdaORegion at ord = F(ord) * O_hol;
* paperSkeletonQPilotLog = mu_log(paperSkeletonQPilotRegion).

Theorems (all actual, no sorry/axiom):
* paperQPilotExponentFamily_nonneg;
* paperRootCoefficientFamily_le_qPilot  (ord/(2l) <= ord);
* paperSkeletonQPilotRegion_measure_pos_lt_top;
* paperSkeletonQPilotLog_eq  (mu_log(F(ord)) = -ord log p);
* paperSkeletonQPilotLog_eq_neg_valueGroupSkeletonLength;
* paperLeastLambdaOHull_subset_holomorphic;
* paperLeastLambdaOHull_measure_lt_top;
* paperSkeletonQPilotRegion_subset_leastHull;
* paperLeastLambdaOHull_measure_pos;
* **paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog** (unconditional
  comparison, the main new paper-level inequality);
* paperLeastLambdaOHullLog_le_zero;
* **paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator** (exact
  quantised computation);
* **paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization** (strict
  defect, no-go for the naive formula).

Verification: local compilation passed via tools/lean_auto.py audit --fresh
(exit 0, status green, no error/warning lines); build log
D:/lean/tmp/lean-automation/build-ebd1c796483a4ee2a5abfc61c43a65b2.log,
cmd exit=0 total=354.3s.  The file's #print axioms for the four main theorems
all report exactly [propext, Classical.choice, Quot.sound] (no sorryAx).
This is a local compile check, not a project-wide axiom audit; project-level
acceptance still requires the batch build and the ledger integration, which
belong to the parent/integrator.

## 9. References (same as S729 plus the value-group/quantisation point)

* Bosch, Lutkebohmert, Raynaud. Neron Models, Ch. 9 (Tate curve, skeleton
  R / v(q)Z).
* Baker, Payne, Rabinoff. On the structure of non-archimedean analytic curves,
  Contemp. Math. 605 (2013) (skeleton of the Tate curve).
* Gubler. Tropical varieties for non-archimedean analytic spaces, Invent.
  Math. 169 (2007) (tropicalisation, value-group picture).
* Chambert-Loir. Mesures et equidistribution sur les espaces de Berkovich,
  J. reine angew. Math. 595 (2006) (canonical measures; different from Haar).
* Nicaise, Xu, Yu. The non-archimedean SYZ fibration, Compositio Math. 155
  (2019) (why the literal SYZ skeleton is a different object).
* For the Haar/lattice computation: IUT IV Proposition 1.4(i) normalization,
  formalized in
  LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean.

## 10. Repo anchors

* tmp/sheaf/xif/paper/S793PaperLeastLambdaOHullActual.lean
* tmp/sheaf/xif/paper/S799LeastLambdaOPaperTargetActual.lean
* tmp/sheaf/xif/paper/S801PaperHullLogActual.lean
* tmp/sheaf/xif/paper/S812LeastLambdaOFiniteLStackActual.lean
* tmp/sheaf/xif/paper/S782FiniteRootStackExtensionActual.lean
* tmp/sheaf/xif/paper/S779RootHullNonzeroFixActual.lean
* tmp/sheaf/xif/paper/QVFamTensorCoefficientActual.lean
* tmp/sheaf/xif/paper/QVFamRootFactorCorrectionActual.lean
* tmp/sheaf/xif/paper/QVFamNormalizedGeneratorSupplyActual.lean
* tmp/sheaf/xif/paper/QVFamNormalizedCoefficientOrderAuditActual.lean
* tmp/sheaf/xif/paper/RootHullMeasureActual.lean
* tmp/sheaf/xif/paper/UnitSmulCanonicalUnitReferenceActual.lean
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean
* LeanFormal/IUT/Foundations/LocalFields/PadicFractionalLattice.lean
* tmp/sheaf/xif/paper/S815PaperScalingDataFiniteLActual.lean
* tmp/sheaf/xif/paper/S819PaperRootCompletionGeneratorActual.lean
* tmp/sheaf/xif/paper/S814SkeletonQuantizedLeastHullActual.lean (this task)
