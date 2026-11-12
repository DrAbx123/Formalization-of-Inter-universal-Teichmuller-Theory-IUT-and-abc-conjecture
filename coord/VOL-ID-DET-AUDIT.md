# VOL-ID-DET-AUDIT — theta/q 体积识别与 det–qroot 链接审计（A1058）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`coord/VOLUME-IDENTIFICATION.md`、`coord/QROOT-DET-LINK.md`；约定：`negHaarLog`（S2717/S2807 使用）。

## 0. 约定与目标

* `haarLogVolume mu S := Real.log ((mu S).toReal)`（Mathlib `Mzk1XiEContainmentMonotoneActual:75` 同型）；
* `negHaarLog mu S := - haarLogVolume mu S`；
* 目标（S2717）：`S2717QPilotLogVolume ≤ S2717ThetaHullLogVolume`；
* 若两者都表示为 `negHaarLog`：`qLog = -H(q)`, `thetaLog = -H(theta)`，其中 `H=haarLogVolume`。

## 1. VOLUME-IDENTIFICATION 方向审计

### 1.1 方向是否正确

`H = haarLogVolume` 是 measure 的 log；measure 单调：`S⊆T ⇒ mu S≤mu T`，log 递增 ⇒ `H S≤H T`。
因此：
```
-(H q) ≤ -(H theta)  ⇔  H theta ≤ H q
```
由 `theta ⊆ q` 得 `H theta ≤ H q`，故 `negHaarLog q ≤ negHaarLog theta`；
即 `qLog ≤ thetaLog`（paper 的 `-|log q|≤-|logΘ|`）。
**结论：在 negHaarLog 约定下，`theta⊆q` 是正确充分方向；`q⊆theta` 只给相反不等式。**

文档 §3（:49-60）的推导与此一致：先展开 `-(H q)≤-(H theta) ⇔ H theta≤H q`，再由 `theta⊆q` 用单调性；
并明确警告早期 `q⊆theta` 的 CTHETA-RETARGET-IMPL 说法只属于“无外层负号的 log-measure signed convention”，
对 S2717 的 `-haarLog` 方向必须反转。这个修正**正确**。

### 1.2 循环性与上/下界误用

* 文档假设 `qLogVolume = -(haarLogVolume mu qPilotRegion).toReal` 是**待建立的 identification**（§4/§6 明标 GAP），
  没有假设目标或 `qLog≤thetaLog`；推导只用 measure 单调、log 单调、outer negation；**不循环**。
* 也没有把上界当下界：S2807 给 theta 的精确 `−H(theta)`；q 侧缺区域/等式，文档明确说不能由标量候选推出；
* `haarLogVolume_mono` 被引用为已有；本审计不编译，gate 只能 PENDING-WATCHDOG（不得写 green）；
* 小问题：文档说 “Both ... are negative quantities of form -|log(...)|”；`negHaarLog` 的符号取决于 `mu` 是否 >1，
  方向证明不需要“两者为负”，只需 `H` 单调。建议改成纯公式，避免符号叙述误导。
* `qPilotHaarRegion`、`qPilotLogVolume_eq_neg_haarLog`、`thetaRegion⊆qPilotRegion` 均为**提议的新声明**；
  文档没有声称已存在，§6 明确列 GAP。**判定 PASS（分析级）**。

### 1.3 与 signed-stack 的边界

文档 §5（:103-106）正确指出：`Mzk1SignedLogVolumeCor312Actual` 的 `signedLogVolume=log(vol)` 与
`XiEContainment.q⊆hull` 是**另一套约定**，不能直接用于 S2717 的 `-haarLog`；
这与 A1053 审计一致（signed 栈 q⊆hull，QRegion/negHaarLog 需 theta⊆q）。

## 2. QROOT-DET-LINK 审计

### 2.1 现有定义/事实

* `S3050Unit p jValue l := -((-localNormOrder p jValue)/(2*l))*Real.log p` 是**标量 log-magnitude**，
  不是群单位；`S3050QUnitIdentification Q := ∃ c, S3050Unit = c*Q` 只是 **Prop**，未证；
* `S3016StepVQPilot` 是 q-pilot **line-bundle/ideal** 的 log volume；`S3016WeightedGlobalQPilot` 是 native 标量；
  没有 qroot/scaleElt；
* qroot 只出现在 theta 侧 `HullDetObjectActual` 的标量 `localQrootLogVolume`/`hodgeTwoLthRoot` 幂；
* `S1422.detDataOfHull` 的 unit 是 dependent prime-inverse diagonal unit，与 qroot 的类型/构造不同；
* `scaleElt` 在 `ThetaRegion.lean:136`，未在这些文件使用。

### 2.2 是否只是簿记？

**不是。** 现有对象中：
* `detUnit` 是（各 completion 的）prime-inverse 乘积单位；qroot 是 completion 中的根值/标量；
* 二者类型不同，且没有 theorem 把 qroot 的幂与 det unit 相乘/张量识别；
* 即使 `S3050Unit` 与 `stepVLambda` 都是 `j²*ord/(2l)*log p` 的标量，它们只是 **log 数值**，
  不能替代单位等式；
* 因此 `detUnit = tensorProduct (rootUnit ...) (gaussExponent j)`（或 `∏ incl_i(qroot^{j²})`）
  是**新的实质 identification**，需要 local norm/order bridge 与 tensor/diagonal 等式；
* 若有人把 `detUnit` **定义为** qroot 的幂，则该等式是定义性的，但它不再等价于 `S1422.detDataOfHull`
  的既有 det unit；必须另证与既有对象的相等，否则是换对象/循环。

### 2.3 方向/循环性

* 文档没有提出目标不等式，只做存在性/缺口审计；无方向误用；
* `S3050QUnitIdentification` 是 Prop，不是证明；文档明确说未证；
* 若用 `S3050QUnitIdentification` 反推 `Q`（把 Q 定义成 Unit/c）则**定义性循环**；文档没有这样做，
  而是把 `Q` 作为待识别对象；**无 CIRCULAR**；
* 最小 bridge `rootUnit/detUnit/identification/log-volume corollary` 是实质新声明，不是簿记；
* 未编译，gate PENDING-WATCHDOG。

## 3. 判定汇总

| 文档 | 判定 | 理由 |
|---|---|---|
| `VOLUME-IDENTIFICATION` | **PASS（分析级）** | negHaarLog 下 `theta⊆q` 方向正确；q 侧区域/等式明标 GAP；无上/下界误用；无循环；未冒充定理 |
| `QROOT-DET-LINK` | **PASS（分析级）** | 正确认定 det↔qroot 无现有链接；不是簿记，需新 local norm/tensor identification；未循环 |
| `negHaarLog` 方向 | **PASS（条件）** | `H=log mu` 单调；`theta⊆q ⇒ -H(q)≤-H(theta)` |
| det 单位↔qroot | **不是簿记；GAP-DET-QROOT** | 类型/构造不同；需 rootUnit/detUnit/local norm/tensor equality |

**总判定：两文档均 PASS（分析级）；没有 CIRCULAR；主要风险是符号叙述（negHaarLog vs signedLog）和 det 链的“定义性替换”伪装。**

## 4. 修正/后续 gate

1. VOLUME-IDENTIFICATION 中把 “Both negative” 改成显式 `negHaarLog S := -Real.log ((mu S).toReal)`；
   并明确 `theta⊆q` 是 `negHaarLog` 口径的充分方向，`q⊆theta` 是反向；
2. q 侧仍缺 `qPilotHaarRegion`/`qPilotLogVolume_eq_neg_haarLog`/`thetaRegion⊆qPilotRegion`；
   三者未证前，`S2717QPilotLogVolume≤S2717ThetaHullLogVolume` 不得声称已由 common-mu 推出；
3. QROOT-DET-LINK 的 `rootUnit`/`detUnit` 若用定义构造，必须另证与 `S1422.detDataOfHull` 的相等；
   不得把 `detUnit := qroot^...` 当已有 det unit；
4. `S3050QUnitIdentification` 只能作为待证 Prop；禁止用 `Q:=Unit/c` 反推；
5. 所有 Lean 文件/引用 gate 用 watchdog/mainline；本审计不编译，相关文件一律 PENDING-WATCHDOG。
