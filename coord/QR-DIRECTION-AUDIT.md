# QR-DIRECTION-AUDIT — q/θ 方向、QRegion Inclusions、XID 计划巡检（A1050）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`tmp/sheaf/xif/paper/Mzk1QRegionInclusionActual.lean`（SHA16 `554E8ADC`）、`coord/XID-DETERMINANT-PLAN.md`；并复核 `−A≤−R ⇔ A≥R ⇔ μ(q)≥μ(θ) ⇔ θ⊆q` 的方向。

## 0. 记号与结论先行

按 `logVol S = -log μ(S)`，`A = log μ(qRegion)`，`R = log μ(thetaRegion)`：

* `logVol(qRegion) = -A`，`logVol(thetaRegion) = -R`；
* variant（N5/qRegion 形式）是 `-A ≤ rhs`，在 q/θ 区域读法下 `rhs = -R`，即 **`-A ≤ -R`**。

**结论：前三步等价正确，最后一步 `μ(q)≥μ(θ) ⇔ θ⊆q` 不正确。**
正确链是单向充分：
```
thetaRegion ⊆ qRegion  ⇒  μ(theta) ≤ μ(q)  ⇒  R ≤ A  ⇒  -A ≤ -R
```
其中 `μ(theta)≤μ(q)` 由 measure 单调性得到（需 `μ(q)<∞` 等）；**反向 `μ(q)≥μ(θ) ⇒ θ⊆q` 一般不成立**
（反例：q=[0,1]，θ=[0.5,1.3] 在 Lebesgue 下 μ(q)=1>0.8=μ(θ)，但 θ⊄q）。
所以 `theta⊆q` 是**充分条件**，不是与 `A≥R` 等价的充要条件；若把 `⇔` 写成充要，属于 INVALID 方向断言。

## 1. QRegion Lean 文件审计

### 1.1 事实

* 路径：`tmp/sheaf/xif/paper/Mzk1QRegionInclusionActual.lean`；SHA256 =
  `554E8ADC5D287A854B7BC0929E134EBCBE10E7DA34759197402BD94DC73B5ED3`（SHA16 `554E8ADC`，与 Lead 给的一致）；
* 状态行：**PARTIAL**（abstract skeleton; concrete q-pilot/theta regions are FIELD-ASSUMED）；
* 文本扫描：无 `sorry`/`axiom`/`admit`（只在 header 注释出现 “no sorry and no axiom”）；
* **本审计不编译**；gate 状态未由 mainline/watchdog 提供 ⇒ 只能记 PENDING-WATCHDOG，不能写 green。

### 1.2 定理方向（逐条）

| 声明 | 陈述 | 方向判定 |
|---|---|---|
| `haarLogVolume_mono_of_subset` | `S⊆T`, `μS≠0`, `μT<∞` ⇒ `logVol T ≤ logVol S` | ✅ 正确（`logVol=-log μ`；measure 单调 + log 单调；处理了 `μS>0`/有限性） |
| `rankOne_minimal` | `h : θ⊆q` ⇒ `-absLogTheta ≥ -absLogQ`（即 `-R≥-A`） | ✅ 正确，等价于 `-A≤-R`；只用到 `vol_q/vol_theta` 与 h |
| `q_subset_theta_gives_opposite` | `h : q⊆θ` ⇒ `-absLogQ ≥ -absLogTheta`（`-A≥-R`） | ✅ 正确的反向记录；不是目标方向 |
| `cor312_rankone_conditional` | `θ⊆q` + 两个 volume 恒等式 ⇒ `-R≥-A` | ✅ 条件定理方向正确 |
| `variant_rankone_conditional` | `θ⊆q` ⇒ `-A≤-absLogTheta`（即 `-A≤-R`） | ✅ 与 variant 符号一致 |
| `variant_rankone_conditional_rev` | `q⊆θ` ⇒ `-absLogTheta≤-absLogQ`（`-R≤-A`） | ✅ 正确的反向（错误方向）记录 |

### 1.3 假设与循环性

* `QRegionData` 的 `vol_q : logVol qRegion = -absLogQ`、`vol_theta : logVol thetaRegion = -absLogTheta`
  是 **结构字段（FIELD-ASSUMED）**；文件没有构造实际 q/θ 区域，也没有证明这两条体积恒等式；
* `h : thetaRegion⊆qRegion` 是**显式假设**，文件没有证明它；
* `haarLogVolume_mono_of_subset` 是纯测度/对数单调性，不依赖 variant/N5/SSIneq；
* 因此定理本身**不循环**：它没有假设 `-A≤-R`，而是从 inclusion+volume identities 推出该不等式；
* 但若后续把 `vol_q/vol_theta` 或 inclusion 用目标/variant 来“证”，则会形成循环；当前文件明确标 GAP-N5，
  审计上应禁止把该文件当“N5/Cor312 已证”。

### 1.4 文件头注释的问题（不是定理错误）

文件 header `DIRECTION-VERIFIED`（:12-18）写：
> `A = log μ(q)`, `R = log μ(θ)`，log 严格单调，所以 `A≥R` 等价于 `μ(q)≥μ(θ)`；
> 由 measure 单调性这又是 `θ⊆q`。

其中 `A≥R ⇔ μ(q)≥μ(θ)` 正确；但 **“由 measure 单调性这又是 θ⊆q” 是反向误用**：
measure 单调只给 `θ⊆q ⇒ μθ≤μq`，不给出反向。应改为：
“`θ⊆q` 是充分条件；`μq≥μθ` 本身不足以推出包含关系。”
定理 `rankOne_minimal` 不受影响（它只从 h 推结论），但 header 的“等价”表述必须修正，否则会被误读为
`μ(q)≥μ(θ) ⇔ θ⊆q` 的假充要。

**判定：`Mzk1QRegionInclusionActual.lean` = PARTIAL**（条件定理方向正确；字段/包含是显式假设；
header 的 `⇔` 方向断言有 INVALID 反向；gate 未验证）。

## 2. XID-DETERMINANT-PLAN 方向审计

### 2.1 已改的方向

* §5 Subgoal B、§7 missing declarations、§8 Direction correction 都改为
  **`thetaHullRegion ⊆ qPilotRegion`**：
  * §8 明确写“正确充分包含是 thetaHullRegion⊆qPilotRegion”；
  * 明确说“相反包含 q⊆θ 给出 -A≥-R，是 Cor 3.12 的错误方向”；
  * 与 QRegion 文件的 `variant_rankone_conditional` 一致；
* §5 Subgoal D 的单调性推导正确：`θ⊆q` ⇒ `logVol(q)≤logVol(theta)` ⇒ `-A≤-R`；
* §8 还明确 A1048b 的 `q⊆θ` 说法作废。

### 2.2 仍存在的问题

* §8 末句仍写：`A≥R ⇔ μ(q)≥μ(theta)`；“measure 单调 ⇒ thetaRegion⊆qRegion” 仍是**反向误用**；
  应写成：`thetaRegion⊆qRegion ⇒ μ(q)≥μ(theta)`（充分），不能写“⇒ theta⊆q”作为由测度推包含；
* §3 的 `S2807_thetaHullVolume_eq_haarRegion`/`S2807_paperCor312Full_iff_haarRegion`
  是引用/条件接口，不是已构造的 inclusion；§7 把 `thetaHullRegion_subset_qPilotRegion` 列为 source GAP，正确；
* `haarLogVolume_mono` 标 “already green” 但未给 watchdog/mainline gate 引用；按 A986/A988 只能 PENDING；
* `hpacket` 仍是 explicit hypothesis（§3），不是定理；§3 明确说 determinant comparison 未证，正确；
* 没有循环：计划不假设 N5/variant；Subgoal D 是“inclusion+mono ⇒ target”，属于条件定理。

**判定：`XID-DETERMINANT-PLAN.md` = PARTIAL**（方向已从 `q⊆θ` 改正为 `θ⊆q`；
但 §8 仍保留 `μq≥μθ ⇒ θ⊆q` 的假逆向；green/gate 未验证；inclusion 与 q-pilot 体积恒等式仍 GAP）。

## 3. 方向推导修正后的完整表述

正确的单向链（论文/文件实际需要）：
```
(H1) logVol(qRegion) = -A,  logVol(thetaRegion) = -R          [FIELD-ASSUMED]
(H2) thetaRegion ⊆ qRegion                                  [GAP, Step (xi-d)]
(1)  μ(thetaRegion) ≤ μ(qRegion)          (measure_mono H2)
(2)  R = log μ(theta) ≤ log μ(q) = A      (log 单调；需 μ>0)
(3)  -A ≤ -R                               (代数)
```
不能把 (2) 反过来说成 `A≥R ⇒ H2`；measure inequality 不包含集合包含信息。
若未来只有 `μ(q)≥μ(theta)` 而没有 H2，则只能得到 `A≥R`（即 `-A≤-R`），目标不等式本身仍成立；
但若要证 H2（paper Step xi-d 的几何核心），必须另有“无正测度外部/region 结构”的引理；不能由测度大小反推。

## 4. 判定汇总

| 对象 | 判定 | 理由 |
|---|---|---|
| `−A≤−R ⇔ A≥R` | **PASS** | log 单调、代数正确 |
| `A≥R ⇔ μ(q)≥μ(theta)` | **PASS** | `A=logμq,R=logμtheta`；需 μ>0 |
| `μ(q)≥μ(theta) ⇔ θ⊆q` | **INVALID** | 只有 `θ⊆q ⇒ μθ≤μq`；反向不成立（反例见 §0） |
| `theta⊆q ⇒ −A≤−R` | **PASS（充分条件）** | measure 单调 + logVol=−logμ |
| `Mzk1QRegionInclusionActual.lean` | **PARTIAL** | 条件定理方向正确；volume identities/inclusion FIELD-ASSUMED；header `⇔` 误写；gate PENDING |
| `XID-DETERMINANT-PLAN.md` | **PARTIAL** | 方向已改对（θ⊆q）；§8 残留假逆向；green/gate 未验证；H2 仍 GAP |

## 5. Gate/修正

1. 所有文档把 `μ(q)≥μ(θ) ⇔ θ⊆q` 改为**单向充分**：`θ⊆q ⇒ μθ≤μq`，删除 `⇔`；
2. `QRegionData.vol_q/vol_theta` 与 `h` 必须继续标 FIELD-ASSUMED/GAP-N5；
   不能把 `rankOne_minimal` 当无条件 N5/Cor312；
3. `XID-DETERMINANT-PLAN` §8 的 “measure 单调 ⇒ θ⊆q” 改为 “`θ⊆q` 是充分来源；
   从测度反推包含需要额外结构，不在本计划内”；
4. 任何 green 声明（`haarLogVolume_mono` 等）必须引用 watchdog/mainline gate；本审计不编译，
   相关状态一律 PENDING-WATCHDOG；
5. 若目标是 `−A≤−R`，H2（θ⊆q）足够；若目标是反过来由 `A≥R` 推 H2，则是逻辑错误，不是计划缺口。
