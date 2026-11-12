# SIGNED-DIRECTION-AUDIT — signed-stack 与 q/θ 方向一致性巡检（A1053）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`tmp/sheaf/xif/paper/Mzk1SignedLogVolumeCor312Actual.lean`（`signed_cor312_inequality`、`XiEContainment`），以及 adapter `Mzk1XiEContainmentRequirementActual`/`Mzk1XiEContainmentMonotoneActual`。

## 0. 三套符号必须先固定

### 0.1 QRegion/abc 口径（A1050）
* `logVol S := -log μ(S)`；`A := log μ(qRegion)`，`R := log μ(thetaRegion)`；
* `logVol(qRegion)=-A`，`logVol(thetaRegion)=-R`；
* target：`-A <= -R`；充分几何：`thetaRegion ⊆ qRegion`。

### 0.2 signed-stack 口径（本文件）
* `signedLogVolume vol S := Real.log (vol S)`（第 24-25 行）；
* `XiEContainment.subset : qRegion ⊆ hullRegion`（第 39-44 行）；
* `signedQ := signedLogVolume vol qRegion`，`signedTheta := signedLogVolume vol hullRegion`；
* 定理：`qRegion⊆hullRegion` + `hmono : S⊆T ⇒ vol S≤vol T` ⇒ `signedQ≤signedTheta`。

**关键：0.1 的 `logVol` 是 `-log μ`，0.2 的 `signedLogVolume` 是 `log(vol)`；两者差一个负号。**
QRegion 中 q⊆θ（若 hull=θ）给 `A≤R` ⇒ `-A≥-R`（反向）；signed 中 q⊆hull 给 `signedQ≤signedTheta`（正向）。
两者不是同一几何方向，除非 `vol`/`A` 的符号约定同时翻转。

## 1. `XiEContainment` / `signed_cor312_inequality` 实际内容

`XiEContainment` 只有字段：`qRegion`、`hullRegion`、`subset : qRegion⊆hullRegion`、`q_pos : 0<vol qRegion`；
没有字段说 `signedQ=-A`、`signedTheta=-R`，也没有说 `vol` 是 Haar 测度或 `-log μ`。

`signedLogVolume_mono`（:29-34）：`hmono` + `S⊆T` + `0<vol S` ⇒ `log(vol S)≤log(vol T)`；正确。
`xi_f_signed_direction`/`signed_cor312_inequality`（:57-68）：从上述单调性得 `signedQ≤signedTheta`；
证明正确、**不循环**（只假设 hmono/包含/正性；未假设目标）。
`positive_magnitude_direction_obstruction`（:73-75）：`qVol≤hVol ⇒ -hVol≤-qVol`；正确记录反向。

**但**定理只证 `log(vol q)≤log(vol hull)`，不是无条件 `-|log q|≤-|logΘ|`。
要读成后者，必须额外给 identification：`signedQ=-A` 且 `signedTheta=-R`（或 `vol=e^{-logVol}`）。
`XiEContainment` 没有这个字段，header 却写 “This is exactly `-|log q|≤-|logΘ|`”（:12-13）；
这是**解释性 overclaim**，不是定理内容。

## 2. 方向比较表

| 口径 | signed/logVol | 几何包含 | 结论 | 与 target 关系 |
|---|---|---|---|---|
| QRegion | `-log μ` | `theta⊆q` | `-A≤-R`（A=logμq） | ✅ 同 target |
| QRegion 误用 | `-log μ` | `q⊆theta` | `-A≥-R` | ❌ 反向 |
| signed-stack | `log(vol)` | `q⊆hull` | `log(vol q)≤log(vol hull)` | 抽象单调性；需 identification |
| signed 若 `vol=μ` | `log μ` | `q⊆hull` | `logμq≤logμhull`，即 `A≤R`（A=logμq） | ❌ 与 `-A≤-R` 反向 |
| signed 若 `vol=μ`，令 `A_s=-logμq` | `log μ` | `q⊆hull` | `-A_s≤-R_s`（R_s=-logμhull） | ✅ 但 `A_s=-A`，不是 QRegion 的 A |

**结论（按各自定义）**：
1. `signed_cor312_inequality` 与 abc 的 `theta⊆q ⇒ -A≤-R` **不是同一方向**：
   几何包含是 `q⊆hull`，不是 `θ⊆q`；signed 函数是 `log(vol)`，不是 `-log μ`。
2. 在 `vol=μ`、`A=logμq`、`R=logμθ` 的 QRegion 口径下，signed 定理给 `A≤R`，
   即 `-A≥-R`，与 target 相反；不能当 `-A≤-R` 使用。
3. 只有把 signed 的 `A_s` 定义为 `-logμq`（即 `A_s=-A`）并补 `signedQ=-A_s`、
   `signedTheta=-R_s` 的 identification，才得到 target；这是另一套符号，不能混名。

## 3. q⊆hull 误当 theta⊆q 的风险

**存在，且是当前最大方向风险。**

* paper xi-e 的几何叙述是 “q-pilot possible image lies in Θ-pilot hull” ⇒ `q⊆thetaHull`；
  这正是 `XiEContainment.subset` 与 `XiEContainmentRequirement.q_in_possible/possible_in_hull` 的方向；
* QRegion/abc 的充分几何因 `logVol=-logμ` 反转为 `theta⊆q`；
* 把 `XiEContainment.q⊆hull` 直接接到 QRegion 的 `theta⊆q ⇒ -A≤-R` 上，等于把 `q⊆θ` 当 `θ⊆q`，
  **会翻转结论**；QRegion 侧用 q⊆θ 只得 `-A≥-R`；
* `REUSE-AUDIT-LEDGER` 写 “signed-stack 约定 … `signedQ≤signedTheta`，即 `-A≤-R`”，
  这只是 signed 的 `A_s=-logμq` 下的结论；按 QRegion 的 A 不成立，应拆成两套 A/R；
* `Mzk1XiEContainmentMonotoneActual` 的 `qPilotContainerRegion = thetaPilotHull`（:59-70）
  是**恒等包含**（A525 已警告），即使调用 signed 单调性也是 `x≤x`，不是 genuine q/θ 比较。

## 4. 其他检查

* **接口字段当证明**：`subset`/`q_pos` 是字段；`signed_cor312_inequality` 只从字段推结论，
  属条件定理；没有把 `XiEContainment` 的字段当已构造的实际包含。
* **循环性**：`signedLogVolume_mono` 只用 hmono 与 `Real.log_le_log`，不假设 `-A≤-R`/variant；
  `signed_cor312_inequality` 不循环。只有拿目标去证 `XiEContainment` 的实际包含才会循环；文件未构造。
* **sorry/axiom**：文件文本无 `sorry`/`axiom`/`True`/`admit`；未编译 ⇒ gate **PENDING-WATCHDOG**。
* **Requirement** 方向是 q⊆thetaPossible⊆hull（paper xi-e），不是 QRegion 的 θ⊆q；
  `strict_measure : vol q<vol hull` 对应 signed 正向，同样需 signed A_s 定义才能说 target。

## 5. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `XiEContainment`（q⊆hull） | **PARTIAL** | 是 paper xi-e 正确几何方向，但不是 QRegion 的 θ⊆q；仅字段 |
| `signed_cor312_inequality` | **PARTIAL（解释 overclaim）** | 抽象单调性正确且不循环；但 “exactly -A≤-R” 缺 identification；按 QRegion A/R 读会反向 |
| q⊆hull 与 θ⊆q 混用 | **INVALID** | 两包含相反；QRegion 下 q⊆θ 给 `-A≥-R`；不能互换 |
| `Mzk1XiEContainmentMonotoneActual` | **PARTIAL/警告** | `thetaPilotHull=qPilotRegion` 恒等；A525 已警告，不构成 genuine 比较 |
| `REUSE-AUDIT-LEDGER` signed 行 | **PARTIAL** | “signedQ≤signedTheta 即 -A≤-R” 缺 A_s=-logμq 声明；按 QRegion A 不成立 |

**总判定：无 CIRCULAR；但 signed-stack 与 QRegion 不是同一几何方向，且 signed 定理的 target 解释缺 identification。**
必须把两套约定并列写清，不能把 `q⊆hull` 当 `θ⊆q`，也不能把 `signedQ` 直接写 `-A` 而不定义 A。

## 6. 修正建议

1. 在 `Mzk1SignedLogVolumeCor312Actual` header 加约定表：
   `signedLogVolume=log(vol)`；`q⊆hull`；若 `vol=μ` 则 `A_s=-logμq`、`R_s=-logμhull`；
   target 写作 `-A_s≤-R_s`；明确这不是 QRegion 的 `A=logμq`（差负号）。
2. 或增加字段 `signedQ_eq : signedQ=-A`、`signedTheta_eq : signedTheta=-R`（或 `vol=e^{-logVol}`），
   否则 `signed_cor312_inequality` 只能作抽象单调性，不得称 Cor312 方向已证。
3. QRegion/abc 侧继续用 `theta⊆q` + `logVol=-logμ`；不要复用 `XiEContainment.q⊆hull` 去填 QRegion；
   若需 signed 栈，先做 adapter 并证明 `A_QRegion=-A_s`、`R_QRegion=-R_s`。
4. `XiEContainmentRequirement/MonotoneActual` 保留 xi-e 方向（q⊆hull），header 明确“不是 QRegion”；
   `MonotoneActual` 的恒等包含继续标 A525 警告。
5. `REUSE-AUDIT-LEDGER` signed 行拆成 signed 约定（A_s=-logμq, q⊆hull）与 QRegion 约定（A=logμq, θ⊆q），注明不可混用。
6. 所有 green/gate 引用 watchdog/mainline；本审计不编译，相关文件一律 PENDING-WATCHDOG。