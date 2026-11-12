# PORTED-FLT-ASSETS — ported flt 源码可用资产（A506）

updated: 2026-11-11 05:58 (lattice，只读盘点 + 队列操作)

## 0) 来源与转码状态

- 源: `tmp/external/flt-lean`（https://github.com/anthropics/fermats-last-theorem, commit `6e837e75`, 原 toolchain v4.33.1）。
- 已转码到我们固定 4.32.2 的目录: `tmp/external/ported/flt`（19 文件, 精选取自 Definitions）、`flt_core`（234）、`flt_th`（239）、`flt_test`（224）；import 改写为 `tmp.external.ported.flt*.*`，文件头保留来源/license/attribution。
- 转码工具: `tools/transcode_lean_432.mjs`（去 `module`、`public import`→`import`、去 `public` 前缀）已对 ported 全量执行；本轮抽查 10 个目标文件 import 均为 `import Mathlib...`/`tmp.external.ported...`，无 `public import`/`module`。
- 现状: `.lake/build/lib/lean/tmp/external/ported` 已有 **1093 个 olean**（部分已编译）；本轮 `extras_add_closure` 后 `extra-targets` 中 `external/ported/flt` 条目 **177**；watchdog plan（05:47:03）仍为旧计划，下一次 reload 会开始编译新增/重试条目。

## 1) 选中的可用模块（已用 closure 工具入队）

命令: `node tools/extras_add_closure.mjs <10 files>` → 闭包 **84** 文件、新增 **79** 条、队列 total **1119**（含其它队列表项）。

| 模块 | 关键声明/内容 | IUT 相关性 | 状态 |
|---|---|---|---|
| `flt/Definitions/Def_AlgebraicCurve_LocalResidue.lean` | `LocalResidueData`, `CanonicalLocalResidueDataK`, `HasLocalResidue`, `localResidue_of_mem` | **different/局部留数**（IUT IV 的 different、local residue 计算） | 已入队 |
| `flt/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean` | `kaehlerResidueTerm_*`, `weilOfKaehler`, `weilOfKaehler_apply` | **Weil differential/trace/different**（IUT IV log-different、residue pairing） | 已入队 |
| `flt/Definitions/Def_AlgebraicCurve_RegularDifferentials.lean` | `exists_ord_eq_one_and_dCoord_eq`, `regularDifferentials`, `mem_regularDifferentials_iff` | 正则微分/典范除子/different | 已入队 |
| `flt/Definitions/Def_AlgebraicCurve_SerrePairing.lean`（flt 闭包内） | Serre pairing/对偶 | 曲线对偶/留数配对（IUT 的 trace/配对侧） | 闭包入队 |
| `flt/Definitions/Def_AlgebraicCurve_AdelicIndex.lean`（flt 闭包内） | adelic index | 局部-整体指数/degree（IUT 的 arith degree 计算参考） | 闭包入队 |
| `flt/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`（flt 闭包内） | DivisorClassGroup | 除子类群/RR 基础 | 闭包入队（已有编译 target） |
| `flt_core/Definitions/Def_EllipticCurve_FrobeniusTrace.lean` | `galoisTrace`, `galoisTrace_def`, `IsFrobeniusAt`, `IsFrobeniusAt.mem_decompositionSubgroup` | **椭圆曲线 Frobenius/ℓ-adic trace**（ABC/Frey 侧、Galois 表示） | 已入队 |
| `flt_core/Definitions/Def_FLTPrelim_GaloisRep.lean` | `IsGaloisStable`, `GaloisRepIsIrreducible`, torsion smul 引理 | 椭圆曲线 Galois 表示（ABC 的 ℓ-adic 侧） | 已入队 |
| `flt_core/Definitions/Def_FLTPrelim_FreyPackage.lean` | `FreyPackage`, `hppos/hp0/hp_odd`, `gcdab_eq_gcdac`, `hgcdac` | **Frey 曲线/abc 反证结构**（ABC/Frey 相关） | 已入队 |
| `flt_core/Definitions/Def_HeckeGalois_EichlerShimura.lean` | `HeckeAlg`, `heckeGen`, `eigenIdeal`, `mem_eigenIdeal_iff` | Hecke 代数/模性（中长期；当前 IUT 对象暂不直接依赖） | 已入队 |
| `flt_th/Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean` | `AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed` | **Riemann–Roch（函数域）**（曲线 degree/height、P1 工具） | 已入队（注意 `import Mathlib` 全量，OOM 风险） |
| `flt_th/Theorems/Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean` | Cech RR（genus reached） | RR/Cech 上同调（曲线工具） | 已入队 |

## 2) 相关性说明（IUT 对象映射）

- **different/局部留数/Weil differential** → 对应 IUT IV 的 different 上界（不/顺/暴分岐）与 log-different 计算；`LocalResidueData`/`weilOfKaehler` 可作为具体公式的来源。
- **DivisorClassGroup/AdelicIndex/Riemann–Roch** → 曲线除子、degree/adelic 指数工具；对 P1/height、有限性/degree 归约有用。
- **FrobeniusTrace/GaloisRep/FreyPackage** → 椭圆曲线 ℓ-adic 表示/Frey 曲线结构；与 ABC/Frey 反证、Hecke/模性侧相关。
- **HeckeAlg/EichlerShimura** → 模性方法（当前 IUT/abc 形式化长期可能使用；短期不阻塞）。

## 3) 编译监看与风险

- 已入队但 plan 旧（05:47:03）；下一次 plan reload 后按 START/FAIL/DONE 盯；不手动编译、不碰 watchdog。
- **OOM 风险**: `flt_th` 文件 `import Mathlib`（全量 Mathlib）；与 Takkun 并发时可能再触发 OOM。若失败，优先编译 `flt`/`flt_core` 定义层，`flt_th` 延后或按需拆 import（转码脚本之外的人工收窄需 Lead 批准）。
- **API 差异**: 源为 4.33.1，转码只做语法级改写；4.32.2 Mathlib API 可能不同，编译 FAIL 时按 per-file 日志判断是 Mathlib 差异还是内容错误。
- 这些是真实可复用地基（非空壳/非 Prop 恒等）；引用时注明 `tmp.external.ported.flt*` 与来源 commit。
