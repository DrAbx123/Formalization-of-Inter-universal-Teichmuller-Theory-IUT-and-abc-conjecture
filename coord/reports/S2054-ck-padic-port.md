# S2054 — ContinuousKummerTheory port: Kummer.PAdic

日期：2026-11-02（Asia/Shanghai）
工作目录：D:\lean
目标：`ContinuousKummerTheory.Kummer.PAdic` 直接 `lean` 编译 EXIT=0（或精确错误清单）。
结论：**EXIT=0，无错误、无警告；olean 已导出；公理仅 propext / Classical.choice / Quot.sound。**

## 1. 目标与结果

| 项 | 值 |
|---|---|
| 模块 | `ContinuousKummerTheory.Kummer.PAdic` |
| 源文件 | `tmp/local-cft-port/continuous-kummer-theory/ContinuousKummerTheory/Kummer/PAdic.lean` |
| 源文件大小 | 12171 B |
| 源文件 SHA256 | `474B8A2DF407747B75C749E640C0EA80CE389FAF3D5AE7AAE7B0675F799606DA` |
| 源文件 mtime | 2026-10-12T06:36:39（未改动） |
| 编译 EXIT | **0**（attempt 1/4，77.9 s，stdout/stderr 均空） |
| olean | `D:\lean\.lake\build\lib\lean\ContinuousKummerTheory\Kummer\PAdic.olean` |
| olean 大小 | 770360 B |
| olean SHA256 | `5C8A0EA684AAAA4B91F535C2C368E4D672C0CCE4D058C0D5C420A91D6AD2B8CF` |
| 错误清单 | 空（EXIT=0，无需错误清单） |

## 2. 环境与精确命令

- 工具链：`leanprover/lean4:v4.32.2`；Lean 4.32.2，commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`。
- Mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`（D:\lean/lake-manifest.json 的 v4.32.2 pin）。
- 源根（-R）：`D:\lean\tmp\local-cft-port\continuous-kummer-theory`；该副本与 lakefile 注册的
  `continuous-kummer-theory-main` 的 PAdic.lean 逐字节相同（FC: no differences）。
- 命令模板（cwd = D:\lean）：

```powershell
lake env lean -j1 -R D:\lean\tmp\local-cft-port\continuous-kummer-theory \
  -o D:\lean\.lake\build\lib\lean\ContinuousKummerTheory\Kummer\PAdic.olean \
  D:\lean\tmp\local-cft-port\continuous-kummer-theory\ContinuousKummerTheory\Kummer\PAdic.lean
```

`lake env` 提供 LEAN_PATH = 各 package build dirs（Mathlib 等）+ `D:\lean\.lake\build\lib\lean`；
输出 olean 直接落到工程 build dir，模块名保持 `ContinuousKummerTheory.Kummer.PAdic`。

## 3. 依赖锥（PAdic 依赖闭包，全部绿）

| 模块 | 源 SHA256 | EXIT | olean B | olean SHA256 | 备注 |
|---|---|---|---|---|---|
| Kummer.Limit | —（前序绿） | 0 | 1029160 | — | 2026-11-02 01:01:46 |
| Kummer.ZHat | `BE2082C8C57997E08796D0995D567430BFE0BC82C127F7979F4B6D72FE434B39` | 0 | 814216 | `C50E8B0B2DD768552AC792CDB67CB4A603A0FFEF3F49CBEA7F1A7D7A714660BF` | 并行 worker 于 01:17:06 产出；本任务经 PAdic 导入验证可用 |
| Kummer.ProfiniteCompletion | `CC3B82D654B2D32508FCA1FBC2BB4061EFED7A1F98F6067640DDCA07088BCF62` | 0 | 375800 | `38ED08B178708530DF2CA1301AC4BE4EF759A58360B2F1699822C5D9E0D79E6E` | 本任务编译，74.0 s |
| Kummer.PAdic | `474B8A2D...` | 0 | 770360 | `5C8A0EA6...` | 本任务编译，77.9 s |

说明：
- 编译 PAdic 时 ZHat / ProfiniteCompletion 均以 .lake build dir 中 olean 形式解析，无源码再编译。
- 另观察到并行 worker 于 01:21:46 用 `-main` 源副本重编 PAdic，产出 **字节完全相同**
  （同 size、同 SHA256），说明构建可复现；共享产物未被破坏。同一时段 ZHat/Corestriction/CorRes/
  Topology/Values/Specialization/Decomposition/root 也在被并行 worker 依次推进（最终状态见 §8）。
- 瞬时 IO 错误重试逻辑已就位（脚本最多 4 次，遇 failed to read file / locked 等退避重试）；
  本次 attempt 1 即成功，未触发重试。

## 4. 公理审计（`#print axioms`，EXIT=0）

审计文件：`tmp/local-cft-port/_s2054_axiom_check.lean`，日志：
`tmp/local-cft-port/_s2054_logs/PAdic.axiom_check.log`（EXIT=0）。

所有 10 个公开声明均为 **仅** `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`、无自定义 axiom：

- `KummerTheory.mem_pow_smul_top_iff`
- `KummerTheory.exists_fixedPoint_of_adicContraction`
- `KummerTheory.one_add_pow_eq`
- `KummerTheory.exists_pow_eq_one_add`
- `KummerTheory.finiteIndex_powRange_of_isDiscreteValuationRing`
- `KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing`
- `KummerTheory.kummerZHatEquivProfiniteCompletion`
- `KummerTheory.kummerCompletionEquivProfiniteCompletion`
- `KummerTheory.padicKummerZHatEquiv`
- `KummerTheory.instFiniteKummerQuotientsPadic`

目标类型锁定（`#check`）：

```
padicKummerZHatEquiv : (p : ℕ) → [Fact (Nat.Prime p)] →
  ContH1 Gal(AlgebraicClosure ℚ_[p]/ℚ_[p]) (ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p])) ≃*
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of ℚ_[p]ˣ)

finiteKummerQuotients_of_isDiscreteValuationRing :
  ∀ (R K) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K], FiniteKummerQuotients K

instFiniteKummerQuotientsPadic : ∀ (p : ℕ) [Fact (Nat.Prime p)], FiniteKummerQuotients ℚ_[p]
```

消费者侧实例合成同样通过（EXIT=0）：
`FiniteKummerQuotients ℚ_[p]`、`Finite (ResidueField ℤ_[p])`、
任意 CharZero 的 `IsNonarchimedeanLocalField K` 的 `FiniteKummerQuotients K`，
以及以目标类型直接调用的 `noncomputable example ... := padicKummerZHatEquiv p`。

## 5. 验收字段

- `statement_compiles` = **true**（olean 中语句与 `#check` 输出一致）
- `proof_body_checked` = **true**（Lean kernel 逐项检查，olean 导出成功）
- `kernel_closed` = **true**（无 sorryAx；公理仅允许三元组）
- `target_accepted` = **true（port 级）**：EXIT=0 + olean 可导入 + 公理仅三元组。
  这不是原文语义/comparator 级验收：本次为 1:1 未改动上游源码的移植，未做源语义重审，也未跑全 Project 构建。

## 6. 源文件与产物

- **未修改任何 .lean 源文件**：continuous-kummer-theory 下 19 个 .lean 的 mtime 仍为 2026-10-12 06:36:39；
  PAdic.lean 的 SHA256 在编译前后一致（474B8A2D…）。
- 新建脚本/日志（均在 tmp/local-cft-port 下，不属他人文件）：
  - `_s2054_build.ps1` — 编译驱动（-j1、4 次退避重试、summary.tsv）
  - `_s2054_axiom_check.lean` / `_s2054_logs/PAdic.axiom_check.log` — 公理与类型审计
  - `_s2054_strict.ps1` / `_s2054_strict/PAdic.olean` — 严格选项复编（见 §7）
  - `_s2054_root_check.lean` — 全链导入交叉验证（见 §9）
  - `_s2054_watchroot.ps1` — root olean 等待脚本
  - `_s2054_logs/summary.tsv` 及各次 attempt 的 stdout/stderr

## 7. 编译严格性复核（可选交叉验证）

直接 `lean` 不应用 lakefile 的 `[leanOptions]`，为排除“仅因直编宽松才通过”的可能，另以包选项
（`-DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true`）把 PAdic 复编到
`tmp/local-cft-port/_s2054_strict/PAdic.olean`（不覆盖共享产物）：

- STRICT EXIT=0，78.3 s，stdout/stderr 空；
- 产物 770360 B，SHA256 `5C8A0EA684AAAA4B91F535C2C368E4D672C0CCE4D058C0D5C420A91D6AD2B8CF`
  — 与正式 olean **逐字节相同**。

## 8. 全链状态（报告定稿时）

撰写初稿后，并行 worker 继续推进并完成剩余链；截至 2026-11-02 01:26，
`ContinuousKummerTheory` 全部 19 个模块 olean 均在 `.lake/build/lib/lean/` 中：

| 模块 | olean B | 完成时间 |
|---|---|---|
| ContH1.Comparison | 1427912 | 00:49:24 |
| ContH1.Corestriction | 408144 | 00:51:44 |
| ContH1.Basic | 631504 | 00:52:53 |
| Hilbert90 | 337128 | 00:52:56 |
| ContH1.CorestrictionIndep | 393824 | 00:54:56 |
| Kummer.Basic | 611304 | 00:57:06 |
| Kummer.Equiv | 317032 | 00:59:07 |
| Kummer.Limit | 1029160 | 01:01:46 |
| Kummer.Restriction | 532184 | 01:03:40 |
| Kummer.CorRes | 138624 | 01:16:36 |
| Kummer.ZHat | 814216 | 01:17:06 |
| Kummer.ProfiniteCompletion | 375800 | 01:17:54 |
| Kummer.Corestriction | 617752 | 01:18:46 |
| Kummer.Topology | 460912 | 01:19:10 |
| Kummer.Values | 235080 | 01:20:24 |
| Kummer.PAdic | 770360 | 01:21:46（本任务产物同一 SHA，见 §1） |
| Kummer.Specialization | 1146088 | 01:23:11 |
| Kummer.Decomposition | 500792 | 01:24:35 |
| ContinuousKummerTheory（root） | 3400 | 01:25:53 |

根模块 olean SHA256 = `3A0D8C39F0204308AB42B36634D2937A9070C7228084287F442BC6DA0D02DA04`。

本任务直接负责编译的是 `Kummer.ProfiniteCompletion` 与 `Kummer.PAdic`；其余为并行 worker
产物（其中 ZHat 与本任务 PAdic 直接相关，已随导入验证）。

## 9. 全链集成交叉验证

`tmp/local-cft-port/_s2054_root_check.lean`：

```lean
import ContinuousKummerTheory
#print axioms KummerTheory.padicKummerZHatEquiv
#print axioms KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing
#check @KummerTheory.padicKummerZHatEquiv
#check @KummerTheory.kummerZHatEquivProfiniteCompletion
```

运行 `lake env lean`：**EXIT=0**，无导入错误；经根模块导入后公理仍仅
`[propext, Classical.choice, Quot.sound]`；`padicKummerZHatEquiv` 类型与 §4 一致
（仅显示层多出 `↑...toProfinite.toTop` 强制转换）。

## 10. 结论与下一步

- Kummer.PAdic 目标达成：EXIT=0、olean 可导入、公理三元组、严格选项复编同字节。
- PAdic 依赖锥（Limit → ZHat → ProfiniteCompletion → PAdic）与全链 root 均已绿。
- 建议的后续（非本任务范围）：把 root olean 纳入全 Project 构建验收；
  对 S2027/M2a 消费者实际调用 `padicKummerZHatEquiv` 的接口做 comparator/类型锁定验收。
