# NEW-MATHLIB-NUMBER-THEORY — v4.33.1 数论新引理扫描（A506）

## 现状（无法直接扫描的原因，附证据）
- 指定路径 `tmp/external/flt-lean/.lake/packages/mathlib` **不存在**（`Test-Path`=False；`tmp/external/flt-lean/.lake` 也不存在）。flt-lean 只有 `lean-toolchain=leanprover/lean4:v4.33.1` 与 `lake-manifest.json`（mathlib rev = `db584cd6d46c92f209a44c0f1c829460d327499d`），**没有 mathlib 源码/olean**。
- 本机可用的 Mathlib 源码快照均为更旧版本：`tmp/external/iut4-sec1/.lake/packages/mathlib`（lean v4.32.0，8,795 .lean）、`Takkun-IUT_LEAN`（v4.31.0，8,688）、`promachina-iut-lean`（v4.30.0，4,776）；主构建 `.lake/packages/mathlib` 为 v4.32.2。
- 因此**目前无法产出 v4.33.1 新增 file:decl 的真实清单**（不能凭记忆/推测编造）。

## 完成扫描的最短路径
1. 取源：`git clone https://github.com/leanprover-community/mathlib4.git` 并 `git checkout db584cd6d46c92f209a44c0f1c829460d327499d`（或 `lake update` flt-lean 拉取 `.lake/packages`）。
2. 定向 diff（只比我们需要的目录，避免全量）：
   - `Mathlib/NumberTheory/**`（高度、素数计数、Chebyshev、显式界、类域/数域）
   - `Mathlib/RingTheory/DedekindDomain/Different*`、`Mathlib/FieldTheory/FunctionField/Different*`
   - `Mathlib/AlgebraicGeometry/EllipticCurve/**`、`Mathlib/NumberTheory/EllipticCurve/**`（如有新增 naiveHeight/height API）
   - `Mathlib/MeasureTheory/Measure/**`、`Mathlib/Data/ENNReal/**`（Gap 2 的 toReal/Haar 引理）
   - `Mathlib/RingTheory/Etale/**`、`Mathlib/CategoryTheory/Galois/**`（我们的 fiber-functor 前置）
3. 提取新增/改动声明：`diff -r` + grep `^(theorem|def|lemma)`，与 4.32.2 同名声明对照签名。
4. cherry-pick 到 `tmp/newmathlib/<原路径>`，import 改写为 `Mathlib.*`（4.32.2 backport），入队用 `extras_add_closure.mjs`。

## 待扫描主题清单（与 hcomp Gap1/2 直接相关）

| 主题 | 4.32.2 现状（已有基础，不需外找） | v4.33.1 潜在收益 |
|---|---|---|
| p-adic 范数/log 读法 | `Padic.norm_p` 等（O1 已用 `qPilotValue_norm`） | 4.33.1 若有 `Padic.norm_p_pow`/log 引理可直接替换 O1 手证 |
| 素数计数/Chebyshev | Takkun Diophantine 提供 `theta_le`、`primeCounting_le_chebyshev` | 4.33.1 若有 PNT/显式界改进可强化 Gap 2 常数 |
| different/discriminant | ported FLT `RegularDifferentials`/`CanonicalDivisor`（A505 文档） | 4.33.1 若有 Dedekind different 新引理，替换 ported 冗余 |
| 高度 API | 自有 `Height.logHeight₁`（ABCBridge） | 4.33.1 若新增绝对高度/椭圆高度接口，可作 Gap 1 对象层来源 |
| ENNReal/toReal | 已验证 `toReal_mono`、`toReal_ofReal`、`le_ofReal_iff_toReal_le`（A502 适配用） | 4.33.1 若新增 toReal 组合引理，可缩短 A502 手证 |
| 椭圆曲线高度/导子 | 未使用 | 若新增 `naiveHeight`/`conductor`，作 Gap 1 的高度位置参数化 |

## 适配方案模板（待源码到位后执行）
1. 只 cherry-pick 单个声明及其直接依赖链（用 `#check`/`import` 闭包确认），不整文件复制；
2. 文件头改写：`import Mathlib...` 保持不变；若 4.33.1 引用了新增 API，则连同最小依赖一起移植；
3. 4.33.1→4.32.2 常见坑：lemma/instance 重命名（`toReal_*`、`inst*`）、`@[simp]` 属性变化、deprecated alias、`Function.iterate_*` 类；以 per-file watchdog 日志修；
4. 移植后先作为独立文件 `tmp/newmathlib/...` 在 4.32.2 编译（extras_add_closure 入队），不直接改主构建依赖；
5. 命中 Gap1/2 的引理最终以 A502 适配（ENNReal↔ℝ）接入；仍不把任何常数引理当 Gap 证明。

## 结论
- 本轮**无法**给出 v4.33.1 新 file:decl 清单：源码不在本地（仅有 rev 指针）。
- 已给出可复现的取源/diff/cherry-pick/backport 流程与待扫描主题表；源码一到位即可按此执行。
- 现有可用基础不变：Mathlib 4.32.2 + ported FLT different/curve 资产 + Takkun Diophantine 常数 + 自有 ABCBridge Height。

## A506 澄清（取代上面“取 v4.33.1”方案）
- 项目**固定 Mathlib 4.32.2**，不升级、不扫描 v4.33.1。
- 正确做法：把较新外部源码（flt-lean/TauCeti/Takkun 等）用 `tools/transcode_lean_432.mjs` 转码到 4.32.2（去 `module`、`public import`→`import`、去 `public`），已对 `tmp/external/ported`（2,163 文件/1,447 改动）与 `tmp/sheaf/takkun` 执行。
- 数论/高度侧可复用模块来自 **ported flt 源码**（`tmp/external/ported/flt*`）；用 `node tools/extras_add_closure.mjs <files...>` 把模块 import 闭包入队编译。
- 本轮已入队：different/曲线基础 5 模块闭包（closure 7）+ Weil 微分/正则微分定理 2 模块闭包（closure 96），合计 queue +98（总 1,038）。
