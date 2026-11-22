# W11 memo: mu_{2l} group action, fixed points, Lefschetz, and the log

Date: 2026-10-30
Status: research memo + compiled Lean no-go; no fake carrier, no surrogate target,
no change of target.
Companion kernel: tmp/sheaf/xif/paper/W11GroupActionFixedPointNoGoActual.lean.

Related files: S782FiniteRootStackExtensionActual.lean (actual finite root stack
L(mu_{2l}) and the action), S824RootStackyHaarVolumeActual.lean (actual
mu_{2l}-invariant Haar and branch independence), W3RootStackTraceIndexActual.lean
(finite regular representation, trace character, fixed-point count),
TASK_F_EQUIVARIANT_ORBIFOLD_MEMO.md (free torsor, quotient, no norm/log in
equivariant homotopy/K-theory/Bredon), W8ConfigurationSpaceNoGoActual.lean (no
homeomorphism-invariant p-adic log), S342/S719 (completion 2l-th root impossible),
S689_GAUSS_ORBIT_MEMO.md (the mu_{2l}-orbit average of the theta value is zero).

## 0. Executive verdict (Chinese)

**结论：拒绝 fixed point / Lefschetz / Borsuk-Ulam 路线。**

对实际载体逐条核对后，结果是：

1. **没有 fixed root。** mu_{2l} 的非平凡生成元 stackMuUnit 在 S782 的有限根栈
   上作用自由；S782 的 root-stack carrier 上没有任何不动点（kernel:
   stackMuAction_no_fixed）。在扩域 L 上，该生成元的固定集恰好是 {0}
   （stackMuElem_fixedPoints_eq_singleton）。实际根 stackRootUnit 非零，
   所以它不在固定集中（stackRootUnit_not_fixed, no_fixed_point_is_root）。
   固定点定理若可用，选出的也只是 0，不是 root。

2. **真正的 Lefschetz 数就是零。** 在有限正则纤维 mu_{2l} 上，Lefschetz 数
   = 置换矩阵的迹 = 不动点个数。W3 已经 kernel-checked：Tr(a) = 2l（a = 0），
   Tr(a) = 0（a != 0）（matrixTrace_regularPerm, traceCharacter_eq_delta）；
   本包另给 lefschetzNumber_nontrivial_eq_zero 与
   fixedPoints_nontrivial_eq_empty。所以非平凡群元素的 Lefschetz 数为 0，
   固定集为空。这条路在真实数学上是 "Lefschetz 数为 0"，不是 "找到不动点"。

3. **平均代表是 0，不是 root。** 对实际根轨道取等权代数平均:
   sum_{k=0}^{2l-1} zeta^k * r = 0（有限几何和，rootOrbitSum_eq_zero），
   故平均为 0（rootOrbitAverage_eq_zero），而 0 不是 root
   （rootOrbitAverage_ne_root）。这不是拓扑定理，只是有限几何和/线性平均。
   S689 的 Gauss 计算还表明：对非零 label，theta 值的 mu_{2l} 平均也是 0；
   所以 "平均 theta 值" 连 theta 值都找不回来，只有 modulus/log 存活。

4. **Borsuk-Ulam 类比不成立。** 需要的对象是一个连续映射 S^n -> R^n 的
   奇性/对径点重合；本问题里的 log 是整个 mu_{2l} 不变的函数
   （rootLog_branch_independent），Borsuk-Ulam 的结论对每个点自动成立，
   没有任何算术信息。把 "log 不变" 改写成 "对径点有相同 log" 只是换皮，
   不是使用 Borsuk-Ulam。

5. **log 不变是度量事实，不是拓扑定理。** 对 zeta in mu_{2l}，
   ||zeta|| = 1（有限阶元素在 normed field 中范数为 1），所以
   ||zeta * r|| = ||r||；又 r^(2l) = q，故
   log ||r|| = (1/(2l)) log ||q||。这些是本包与 S824 的实际定理
   （rootLog_eq_inv_card_mul_qLog, stackRootLog_eq_inv_card_mul_qLog,
   stackRootLog_branch_independent），但证明只用 norm 的乘性，没有使用任何
   拓扑/同调定理。

6. **paper least hull 上没有 mu_{2l} 作用。** S793/S799 的 least lambda*O
   hull 是 completion tensor block qVFamTensorBlock T b 里的集合；S342/S719
   证明 qVFamily 在 completion 中没有 2l-th root，因此 completion block 上
   没有由该 root 给出的 mu_{2l} 作用。真正的 mu_{2l}-空间是 L(mu_{2l}) 根栈，
   不是 paper hull。Task F memo 的 N3 已指出：根栈测度到 completion hull
   没有 algebraic/measure-preserving transport。于是 "在 hull/compact space
   上找 fixed point" 这条路线在 paper hull 上连作用都没有定义；在根栈上则有
   作用但固定集是 {0}。

因此：拒绝该路线作为消除 root ambiguity 或证明 log invariant 的方法。
真正可用的不变对象是函数/集合（norm、closed ball、Haar measure），不是
不动点；1/(2l) 的测度版本已经由 S824 的 fundamental-domain/Haar 定理给出，
但那是测度论，不是 fixed-point 拓扑。

## 1. 任务设定与被检验的四种解释

Task W11 提议：用 mu_{2l} finite group action 在 hull/compact space 上，找
fixed point / invariant representative（Lefschetz / averaging / Borsuk-Ulam
类比），从而消除 root ambiguity 并证 log invariant。

可能的解释有四种，本包逐一核对：

| 解释 | 实际对象 | 结果 |
|---|---|---|
| fixed point of the mu_{2l}-action | S782 root stack / L | 无固定 root；L 上固定集 = {0} |
| Lefschetz fixed point theorem | 有限正则纤维 mu_{2l} | L(a)=0 for a != 0；固定集空 |
| averaging representative | 实际根轨道 zeta^k * r | 平均 = 0，不是 root |
| Borsuk-Ulam | log 作为 S^n -> R 的映射 | log 已 G-invariant，结论空洞 |

## 2. 实际群作用与固定点

### 2.1 生成元非平凡

S782 用 Classical.choose 从 HasEnoughRootsOfUnity.exists_primitiveRoot 取
primitive 2l-th root stackMuRoot。本包把它展开为：

    stackMuRoot_isPrimitiveRoot :
      IsPrimitiveRoot (stackMuRoot : rootNormedAmbient T b) (2 * l.value)

因为 l >= 5，2l > 1（twoL_gt_one），故 stackMuRoot != 1，从而
stackMuUnit != 1（stackMuUnit_ne_one）。

### 2.2 S782 action 无不动点

S782 的 action:

    stackMuAction (u : StackSectionCarrier T b) =
      (stackMuUnit * u.1, u.2)

若 stackMuAction u = u，则 stackMuUnit * u.1 = u.1，约去 u.1 得
stackMuUnit = 1，矛盾。故：

    stackMuAction_no_fixed : stackMuAction u != u

这是 "free action" 的代数内容：每个非平凡群元素都没有不动点。（对
stackMuUnit^k，k = 1..2l-1，同样由 primitive 性得非平凡；本包只显式写了
生成元，memo 给出一般论证。）

### 2.3 L 上的固定集恰好是 {0}

把 stackMuElem 看成 L 的元素。若 stackMuElem * x = x，则
(stackMuElem - 1) * x = 0；因为 stackMuElem != 1 且 L 是域，故 x = 0。
反过来 0 当然固定。因此：

    stackMuElem_mul_eq_self_iff : stackMuElem * x = x <-> x = 0
    stackMuElem_fixedPoints_eq_singleton :
      {x | stackMuElem * x = x} = {0}

实际根 stackRootUnit 是 unit，非零（stackRootUnit_ne_zero），所以：

    stackRootUnit_not_fixed : stackMuElem * root != root
    no_fixed_point_is_root : fixed x -> x != root

这是本任务最直接的 no-go：fixed-point 方法在 L 上选出的唯一代表是 0，
而 0 不是 root，也没有有限的 root log。

## 3. Lefschetz / trace：真正的计算给出零

### 3.1 有限正则纤维

取 G = ZMod (rootStackIndex l)，rootStackIndex l = 2 * l.value。W3 定义
regularPerm l a : Equiv.Perm (ZMod (rootStackIndex l))，a + x，并证明：

    fixedPoints_regularPerm :
      fixedPoints (regularPerm l a) =
        if a = 0 then univ else empty
    matrixTrace_regularPerm :
      trace ((regularPerm l a).permMatrix R) =
        if a = 0 then (rootStackIndex l : R) else 0

这是真正的 Lefschetz 数：对有限集合上的置换，Lefschetz 数 = 置换矩阵的迹
= 不动点个数。非平凡 a 的 L 为 0，固定集为空；单位元的 L 为 2l，固定集是
整个纤维。

本包在此之上加：

    lefschetzNumber_regularPerm :
      trace = if a = 0 then (rootStackIndex l : R) else 0
    lefschetzNumber_nontrivial_eq_zero : a != 0 -> trace = 0
    fixedPoints_nontrivial_eq_empty : a != 0 -> fixedPoints = empty
    fixedPoints_identity : fixedPoints (regularPerm l 0) = univ

### 3.2 它为什么不能消除 root ambiguity

Lefschetz 定理的作用是：若 L(f) != 0，则 f 有不动点。这里：

- 对非平凡群元素 a != 0，L = 0，定理不提供任何不动点；事实上固定集为空。
- 对单位元 a = 0，L = 2l != 0，固定集是整个纤维；但这是恒等作用，当然
  固定所有点，不选择 root。
- 所以 Lefschetz 定理在两种情况下都不给出 "一个非平凡的不动 root"。
  有限正则作用本身是 free 的；自由作用没有不动点，这与 Lefschetz 数 0
  完全一致。

如果把这个计算提升到 L 的闭球上：非平凡生成元是有限阶线性等距，其固定集
是 {0}（2.3），Lefschetz 数（非退化情形）为 det(1-T) != 0；Lefschetz 定理
再次只保证 0 这个固定点。这个提升本包没有形式化（需要有限维实 Lefschetz
理论；Mathlib 当前没有 Lefschetz/Brouwer 定理），但它不会改变结论：固定点
是 0。

## 4. 平均 / invariant representative

### 4.1 轨道和为零

令 rootMuElem 为 ambient 中的 primitive 2l-th root，r 为实际根。有限几何和
给出：

    sum_{k=0}^{2l-1} rootMuElem^k * r = 0

kernel: rootOrbitSum_eq_zero。除以 2l（在特征 0 的 L 中可逆）：

    rootOrbitAverage_eq_zero :
      ((2l : L))^{-1} * sum = 0

而 rootOrbitAverage_ne_root 说明 0 != r。因此等权平均代表是 0，不是 root。

注意：这不是 "convex average"（L 是 p-adic field，不是实向量空间；没有
通常的实凸组合）。这是代数等权平均 / 有限几何和。即使用户接受 "averaging"
作为操作，它给出的也是 0，不是 root。

### 4.2 Gauss 平均的额外 no-go

S689_GAUSS_ORBIT_MEMO 已经证明：对非零 label j，theta 值 r^(j^2) 在
mu_{2l} 上的平均是

    (1/(2l)) sum_zeta zeta^(j^2) * r^(j^2) = 0

因为 2l 不整除 j^2。因此：

- 平均 theta 值 = 0，不能恢复 theta 值；
- 只有 modulus / log 存活（||zeta^(j^2)|| = 1）。

这与 Task F memo 的 F3 一致：唯一存活的不变量是 log-modulus，而
log-modulus 是函数，不是 fixed point。

### 4.3 真正的不变代表：ball / norm，不是点

实际可用的不变对象是闭球 closedBall 0 ||r||（以及它的 Haar log）。S824
已证明：

    stackyLogVolume_branch_independent :
      ||zeta|| = 1 ->
        logV (closedBall 0 ||zeta * root||) =
        logV (closedBall 0 ||root||)

本包给 pointwise 版本：

    rootLog_branch_independent :
      zeta^(2l) = 1 -> log ||zeta * r|| = log ||r||
    stackRootLog_branch_independent :
      ||zeta|| = 1 -> log ||zeta * root|| = log ||root||

这是集合/函数层面的 invariant representative：球作为集合在 mu_{2l} 下不变，
log 是球半径的函数。它不是 fixed point of the action；把 "invariant ball"
说成 "fixed point" 只是换皮。S824 的测度定理（fundamental domain / Haar）
是这条路线的真正内容，但那是测度论，不是 fixed-point 拓扑。

## 5. Borsuk-Ulam 类比：为什么是空洞的

Borsuk-Ulam 的典型形式：连续 f : S^n -> R^n，存在 x 使 f(x) = f(-x)。
本问题中：

- log ||zeta * r|| 对整个 mu_{2l} 不变，特别对 zeta = -1 不变；所以对每个
  x 都有 f(x) = f(-x)，Borsuk-Ulam 的结论自动成立。
- 如果只取 -1 subgroup，Borsuk-Ulam 给的是 "log 在 antipodal 点相等"；
  但这是我们已经知道的 norm-one 事实，不是新定理。
- Borsuk-Ulam 不提供任何 p-adic/valuation 信息；它没有 q、order、
  completion scaling data 的输入，不能证明
  log ||r|| = (1/(2l)) log ||q||，更不能证明 paper least hull log 的
  -order/(2l) log p 公式。

所以 Borsuk-Ulam 在本问题中只有 "类比" 价值，没有定理价值。本包拒绝把
它作为证明路线。

## 6. 载体不匹配：paper hull 上没有 mu_{2l} 作用

S793/S799 的 least lambda*O hull 是
paperLeastLambdaOHull (l := l) T b : Set (qVFamTensorBlock T b)，位于
completion tensor block。S342/S719 的核心结论是：qVFamily 在 completion 中
没有 2l-th root（否则 2l | order，与 order 与 l 互素矛盾）。因此：

1. completion tensor block 上没有由 "qVFamily 的 2l-th root" 给出的 mu_{2l}
   作用；论文里的 "Theta value determined up to mu_{2l}" 是根栈/algebraic
   closure 侧的 ambiguity，不是 completion hull 上的 group action。
2. 真正的 mu_{2l}-空间是 S782 的 rootStackExtension T b 和 S824 的 Haar
   measure；它和 paper least hull 是不同类型/不同载体。
3. Task F memo N3 已经指出：root stack 的 measure 到 completion hull 没有
   algebraic/measure-preserving transport；S824 的比较只是 normalized log
   scalar 的比较，不是 pushforward。

所以 "用 mu_{2l} action 在 hull/compact space 上找 fixed point" 在 paper
hull 上连作用都没有。在根栈上作用存在，但固定集是 {0}（第 2 节）。这不是
"还没找到定理"，而是 "对象不匹配"。

## 7. 拓扑为什么看不见 log：W8 的 no-go

W8 已经 kernel-checked：

    no_homeomorphism_invariant_padic_log :
      (F : Set Q_p -> R)
      (hinv : forall homeomorphism h, F (h '' S) = F S) ->
      not (forall k, F (padicBall k) = ballLog k)

证明用 dilation x |-> p * x：它是 homeomorphism，把 unit ball 送到 radius
p^{-1} 的 ball，但 normalized log 改变 -log p != 0。因此任何
homeomorphism-invariant functional（更不用说 homotopy/singular homology
invariant）都不可能等于 log。W11 的 fixed-point/Lefschetz 路线若要证明 log
invariant，必须产生一个拓扑不变量等于 log；W8 说明这不可能。

注意 W8 的模型是 Q_p；paper block 的拓扑/transport 未形式化（W8 已声明
这一点）。但即使只在 local model，也已经足以否定 "用拓扑不变量证 log" 的
路线。fixed-point 定理是拓扑的；它给出的不动点/迹不能携带
-order/(2l) log p 这种度量信息。

## 8. 正结果：log invariant 的实际定理（非拓扑）

虽然 fixed-point 路线被拒绝，log invariant 本身是真的，而且不依赖任何拓扑
定理。本包在 S824 的基础上给出 pointwise 与 stack-unit 版本：

    rootLog_eq_inv_card_mul_qLog :
      log ||rootNormedElement|| =
        (1 / (2 * l.value)) *
          log ||unitToAlgClosed (sourceRootQUnit)||

    stackRootLog_eq_inv_card_mul_qLog :
      log ||stackRootUnit|| =
        (1 / (2 * l.value)) * log ||stackQUnit||

证明只用：

- rootNormedElement_pow / stackRootUnit_pow：root^(2l) = q；
- norm_pow：||root^(2l)|| = ||root||^(2l)；
- Real.log_pow 与 field_simp。

这不是 topology，也不是 homology；它是 norm 的乘性。把它写成 "fixed point
of the scaling action on R" 只是换皮。

paper coefficient order/(2l) 与 spectral c_norm/(2l) 的差别仍然是 S736/S824
的 exact gap；本包不触碰，也不宣称 paper least hull log。

## 9. 结论与可执行的下一步

### 9.1 Verdict

REFUSE. 不接受 W11 的 fixed-point / Lefschetz / Borsuk-Ulam 路线作为消除
root ambiguity 或证明 log invariant 的方法。理由按强度排序：

1. Free action: 非平凡 mu_{2l} 元素在根栈上没有不动点；L 上固定集只有 {0}，
   不是 root。
2. Lefschetz = 0: 真正的有限 Lefschetz 数在非平凡元素上是 0；定理不提供
   不动点。
3. Averaging = 0: 轨道平均是 0，不是 root；Gauss 平均 theta 值也是 0。
4. Borsuk-Ulam 空洞: log 已 G-invariant，结论自动成立，无算术信息。
5. 载体不匹配: paper least hull 位于 completion block，没有 mu_{2l} 作用；
   S342/S719 排除 completion root。
6. 拓扑看不见 log: W8 的 homeomorphism-invariance no-go 直接否定
   "拓扑不变量 = log"。

### 9.2 什么情况下 verdict 会改变

只有在以下情况之一出现时，才值得重新考虑：

- 构造一个非自由的 mu_{2l}-作用在某个 compact/convex carrier 上，且该
  carrier 有到 paper hull 的真实（measure-preserving / log-preserving）
  transport，并且 fixed point 的 norm/log 恰好等于 paper root/hull log。
  当前树中没有这样的 carrier；Task F N3 说明 algebraic transport 不可能。
- 证明一个真正的 topological/homological index theorem，其 index 等于
  -order/(2l) log p，并且 index 的计算不通过 norm/Haar 的换皮。目前没有
  这种工具；W8 说明纯拓扑不变量做不到。
- 把 paper hull 本身替换成根栈上的一个同调/上同调 carrier，并证明该
  carrier 的某个特征类等于 paper coefficient。Task F/S729/S735 已评估过
  equivariant K-theory/Bredon/prismatic 等路线，结论是它们看不到 root
  norm/log；没有新的定理输入。

在这些出现之前，W11 的正确结果是拒绝，而不是继续把 containment/log 改写成
graph/space/fixed-point 的语言。

## 10. Lean inventory（kernel 已验证）

文件：tmp/sheaf/xif/paper/W11GroupActionFixedPointNoGoActual.lean

编译：lake env lean tmp/sheaf/xif/paper/W11GroupActionFixedPointNoGoActual.lean，
EXIT=0（2026-10-30）。仅有一个 linter 风格 warning（simpa 可用 simp），
无 error。

主要声明：

- stackMuRoot_isPrimitiveRoot, twoL_gt_one;
- stackMuUnit_ne_one, stackMuElem_ne_one, stackMuElem_ne_zero;
- stackMuUnit_mul_ne_self, stackMuAction_no_fixed;
- stackMuElem_mul_eq_self_iff, stackMuElem_fixedPoints_eq_singleton;
- stackRootUnit_ne_zero, stackRootUnit_not_fixed;
- w11RootStackIndex, w11RegularPerm, w11_fixedPoints, w11_matrixTrace;
- lefschetzNumber_nontrivial_eq_zero, fixedPoints_nontrivial_eq_empty,
  fixedPoints_identity;
- geom_sum_mul_eq_zero, rootMuElem_isPrimitiveRoot, rootOrbitSum_eq_zero,
  rootOrbitAverage_eq_zero, rootOrbitAverage_ne_root;
- norm_eq_one_of_pow_eq_one, rootLog_branch_independent,
  rootLog_eq_inv_card_mul_qLog;
- stackRootLog_eq_inv_card_mul_qLog, stackRootLog_branch_independent;
- no_fixed_point_is_root, fixedSet_eq_singleton_and_root_not_mem.

#print axioms 实测（以下主声明）：均为
[propext, Classical.choice, Quot.sound]，无 sorryAx：

- stackMuUnit_ne_one
- stackMuAction_no_fixed
- stackMuElem_fixedPoints_eq_singleton
- lefschetzNumber_nontrivial_eq_zero
- rootOrbitAverage_eq_zero
- rootOrbitAverage_ne_root
- rootLog_eq_inv_card_mul_qLog
- stackRootLog_eq_inv_card_mul_qLog
- no_fixed_point_is_root

未运行：独立 comparator、全 Project build。本包只声明本文件的
lake env lean / #print axioms 结果。

## 11. References

- S782: finite root stack L(mu_{2l}), action, root/q sections.
- S824: actual mu_{2l}-invariant Haar, branch independence, q[2u] log.
- W3: finite regular representation trace / fixed-point count / Jones index.
- S689: Gauss orbit average zero.
- S342/S719: completion 2l-th root impossible.
- TASK_F_EQUIVARIANT_ORBIFOLD_MEMO: free torsor; equivariant homotopy/
  K-theory/Bredon cannot see norm/log; stacky measure only normalization.
- W8: no homeomorphism-invariant p-adic log.
- S793/S799: paper least lambda*O hull and its log (completion carrier).