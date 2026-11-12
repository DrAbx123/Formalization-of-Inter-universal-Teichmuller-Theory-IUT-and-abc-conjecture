# TAKKUN PADIC LOG-SHELL：能否替换我们 Lite 模型（A500 只读笔记）

日期: 2026-11-11。对象: `tmp/sheaf/takkun/IutLean/Padic/LogShellRadius.lean`、
`.../LogVolume.lean`（及其同目录 PadicLog/PadicExp/ComplexLog/RealLogKummer/ShellTransport）。
状态: takkun 移植入队 7 个 Padic 文件，尚未编译（results log 无 EXIT，等待 watchdog）。

## 1. Takkun 提供了什么（真实定义 + 已证引理）

### LogShellRadius.lean
- `:39` `aRadius (p e : ℕ) : ℝ := if p = 2 then 2 else ⌈e/(p−1)⌉₊ / e` — [IUT-IV] Prop 1.2 下侧半径常数 aᵢ
- `:44` `bRadius (p e : ℕ) : ℝ := ⌊log(p·e/(p−1))/log p⌋ − 1/e` — 上侧半径 bᵢ
- `:61` `aRadius_tame`（p>2, e≤p−1 ⟹ a=1/e）；`:80` `bRadius_tame`（e≤p−2 ⟹ b=−1/e）；
  `:109` `radius_tame`（a=1/e ∧ b=−1/e）；`:114` `one_div_le_aRadius`；`:126` `le_aRadius`（诚实修正：原文严格 >1/(p−1) 一般假，改为 ≤）；`:139` `aRadius_lt`；`:173/179` `aRadius_one/bRadius_one`。
- 文件自述残余：分岐 e>1 的包含方向、exp 全射、与 different dᵢ 的张量积（Prop 1.1/1.2(ii)）未完成。

### LogVolume.lean
- `:49` `logVol (x : ℚ_[p]) : ℝ := Real.log ‖x‖`（μ_log 归一化：`:52` μ_log(ℤ_p)=0，`:56` μ_log(pℤ_p)=−log p）
- `:62` 乘法性；`:68` `logVol_pow`（θ 值 q^{j²} 的体积形）；`:73` `logVol_p_pow`；`:78` 单调性；
  `:83` `logVol_logOnePlus`（log(1+pℤ_p) 保体积，p>2）；`:91` `logShell_vol_boundary = −aRadius p 1·log p`；
  `:102` `logShellVolFormula p e f m := −(1/e + m/(e f))·log p`（Prop 1.4 (ii)）；`:116` `logShell_vol_eq_formula`（非分岐 e=f=1,m=0）；
  `:133/144` 曲线 11a3 Tate parameter 的具体壳体积。
- 文件自述残余：`log(ℤ_p^×)` 集合本身与公式的同定需 exp 全射性。

## 2. 我们 Lite 模型现状（paper dir grep）

`logShellRadius|aRadius|bRadius|logShellVol|logVol_p|logShellRegion` 在 tmp/sheaf/xif/paper **0 命中**。
我方现有 log-shell 对象是**区域/Haar 型**：
- `C3LogShellTensorPacketActual.actualC3LogShellTensorRegion / actualC3LogShellTensorHaar`（tensor 块上的实际 Haar）
- `S3137C3LogShellPacketNormalizedLogVolumeActual`：`c3TensorBlockDimension`、`c3PacketNormalizedLogVolume_prime_smul` 等 p_v 缩放律
- `S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHullLogVolumeReal`（= log Haar(actual region)）
- `AbsTopIII09ThetaHullScalingActual` re-export 的 p_v 缩放律
即：Lite 模型有"全局 tensor Haar 区域 + dim 缩放律"，但**缺 IUT-IV 局部半径常数 aᵢ/bᵢ 与 μ_log 归一化公式**。

## 3. 判断：可不可以"直接替换"

**结论：不能整体直接替换；可局部替换/补齐，保持我方面对象为主。**
- ✅ 可直接采用（作为真实定义/引理层的替换）：局部 p-adic 归一化 `logVol`（μ_log）与半径常数 `aRadius/bRadius`、公式 `logShellVolFormula`——这些正是我方 Lite 模型缺失的 IUT-IV §1 局部对象；可 import takkun Padic 模块（同属移植依赖待编译）。
- ⚠️ 不能替换：我方 `actualC3LogShellTensorHaar/Region` 是 **tensor/adelic Haar 区域对象**，Takkun Padic 只有逐坐标 ℚ_p 的 log/norm/半径，**没有** tensor packet measure、different dᵢ 张量积、或 Haarlog 区域；文件自述这些恰是残余。
- ⚠️ 需桥接（尚未存在）：把 takkun 的逐坐标 `logVol`/`aRadius` 与 `c3TensorBlockDimension` 的 dim 缩放律对齐需要构造性引理（tensor dim = 坐标维数作用），不能靠定义等价直接换。
- ⚠️ Takkun 自身诚实修正须保留：`le_aRadius`（严格不等式仅部分情形）、`bRadius_tame` 的 e≤p−2 边界、exp 全射性与分岐 e>1 为残余——不能把 takkun 文件当"完整 IUT-IV Prop 1.2/1.4"。

## 4. 建议落地顺序（对象先行，不接线）

1. 等 takkun Padic 模块编译（当前 7 文件在队列）。
2. 新建我们的 O 对象：`PadicLogShellRadiusLaw`（aᵢ/bᵢ 存在且 tame 等式成立）+ `PadicLogVolumeNormalizationLaw`（μ_log 归一化、乘法/幂/保体积公式），字段由 takkun 已证引理构造，配 `_constructed` 定理。
3. 仅在这些对象之后，才写"局部 ℚ_p 归一化 ⇒ tensor dim 缩放律"的桥接引理；不把 takkun 结论当 3.12 证据。
