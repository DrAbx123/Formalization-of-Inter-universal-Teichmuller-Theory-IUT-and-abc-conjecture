# ROUTEB-AUDIT — Route A/B 与域不匹配结论审计（A1066）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`coord/ROOT-COMPLETION-MAP.md`、`coord/ROUTE-A-SCALAR.md`（及其 Lean `Mzk1QPilotVolumeScalarActual.lean`）、`coord/ROUTE-B-BASECHANGE.md`。

## 0. 结论先行

1. **域不匹配结论成立且比 ROOT-COMPLETION-MAP 写的更强**：`rootBase` 是 `T.arithmetic.F` 的 completion，C3 fiber 是 `I.initial.arithmetic.Fmod` 的 completion；`Fmod` 与 `F` 是不同域（有 `Algebra Fmod F`、有限 Galois），所以不存在一般的“base completion 等同”；
2. **Route B 的 `BaseCompletionEquiv` 方向/类型过强**：它要求 `rootBase`（F completion）与 `CommonPrimeCompletion`（Fmod completion）**环同构**；在 `Fmod≠F` 时一般不可能。Route B 不能按现文本视为“type-correct in principle”；
3. **Route A 的 `S3050Unit_eq_log_norm_div` 有符号错误**（按源码定义计算应为 `-log‖x‖/(2l)`），该 Lean 文件未编译；Route A 其余 GAP 诚实，无循环；
4. 未发现 CIRCULAR（没有假设目标推目标）；主要问题是 Route B 的强/错前提与 Route A 的标量符号。

## 1. ROOT-COMPLETION-MAP 的“域不匹配”结论

### 1.1 类型核对（源码）

* `qVFamTensorPlace : NumberField.FinitePlace T.arithmetic.F`（`QVFamTensorCoefficientActual:47`）；
* `rootBase := NormalizedCompletion (qVFamTensorPlace T b)`（`PaperRootCompletionTensorActual:35`）；
* `rootNormedExtension := IntermediateField.adjoin (rootBase) {rootNormedElement}`（`:58-60`）；
* `C3LogShellPlaceL : FinitePlaceAtPrime I.initial.arithmetic.Fmod C3L.p`（`Mzk1C3LogShellTensorLActual:35-37`）；
* `C3LogShellFiberL := CommonPrimeCompletion (C3LogShellPlaceL i)`（`:40-41`）；
* `InitialThetaArithmeticData` 同时有 `Fmod` 和 `F`，并带 `Algebra Fmod F`、`FiniteDimensional Fmod F`、`IsGalois Fmod F`（`ArithmeticData:62-81`）。

因此：`rootNormedExtension` 是 **F-completion 的有限扩域**；C3 fibers 是 **Fmod-completion**。
两者不是同一个基域，也没有给定 `Fmod-completion → F-completion` 的兼容映射；更没有 `Fmod-completion ≅ F-completion`。
ROOT-COMPLETION-MAP 说“rootNormedExtension 是 sourceRootField 的有限扩域，而 C3 是 base completion”**正确**；
但其“base completion”需要再区分 F vs Fmod——这一点在 Route B 中被忽略。

### 1.2 判定

**PASS（分析级）**，但补强：不存在 `rootNormedExtension → CommonPrimeCompletion` 的映射；
更强的障碍是 **F completion 与 Fmod completion 不同域**，不是单纯的“extension vs base”层级差。

## 2. ROUTE-A-SCALAR 审计

### 2.1 已声明的标量核心

* `sourceQPilotSignedLog S := -sourceBadQAbsLog S`；`sourceQPilotSignedLog_eq_neg_badQ` 是 port 恒等式；
* `QPilotVolumeScalarTarget S A := sourceQPilotSignedLog S = -A`；`qPilotVolumeScalarTarget_iff_badQ` 是代数等价；
* 若 `A := OrigXiFPaperBadQAbsLog S`，则 target 由 rfl 成立；文档明确说这**不是** paper 的 `|log q|`（§4.4）；
* GAP-SOURCE-ROOT、GAP-S2691、GAP-S3016 均显式列出，没有伪装为已证。

无循环：没有假设目标；`sourceQPilotSignedLog_eq_neg_badQ` 不依赖 variant。

### 2.2 INVALID：`S3050Unit_eq_log_norm_div` 符号

源码定义：
```lean
S3050Unit p x l := -((-localNormOrder p x) / (2*l:Nat)) * Real.log p
localNormOrder p x := -Real.log ‖x‖ / Real.log p
```
代入：`-localNormOrder = log‖x‖/log p`，
`S3050Unit = -((log‖x‖/log p)/(2l)) * log p = -log‖x‖/(2l)`。
但 Route A 文件/文档写：
```lean
theorem S3050Unit_eq_log_norm_div : S3050Unit p x l = Real.log ‖x‖ / (2*(l:Real))
```
少了负号；按定义这是**假命题**（例如 `ord x=1, p=5`：左边 `+log5/(2l)`，右边 `-log5/(2l)`）。
该文件未编译，文档却把它列为“真证”。**判定：该定理 INVALID（符号错），不能作为 Route A 的 green 输入。**

### 2.3 Route A 总判定

**PARTIAL（含一个 INVALID 定理）**：
* 标量 badQ 归约与 target 等价正确；GAPs 诚实；
* `S3050Unit_eq_log_norm_div` 必须改为 `= -Real.log ‖x‖/(2l)`（或改 `S3050Unit` 定义，不建议）；
* 即使修正，`S3050Unit` 与 paper q 体积的归一化（GAP-SOURCE-ROOT/GAP-S2691）仍未证；不能作为 `-A` 的 paper q 侧证明；
* 未编译 ⇒ gate PENDING-WATCHDOG。

## 3. ROUTE-B-BASECHANGE 审计

### 3.1 设计意图

Route B 把 C3 张量块的 fibers（Fmod 的 `CommonPrimeCompletion`）替换为 root extension `rootNormedExtension T (e i)`，
在 base-changed block 上用 `u := ⨂ u_i` 作乘法，定义 `qPilotBaseChangedRegion := u • rootThetaRegion`，
再证 Haar scaling 和体积。意图正确（绕开 `rootNormedExtension → CommonPrimeCompletion` 的缺失映射）。

### 3.2 关键问题：`BaseCompletionEquiv` 太强/可能为假

Route B §2 要求：
```lean
baseEquiv : ∀ i, rootBase T (e i) ≃+* CommonPrimeCompletion (C3LogShellPlaceL C3L i)
```
`rootBase` 是 **F completion**，`CommonPrimeCompletion` 是 **Fmod completion**；
`Fmod → F` 是有限 Galois 扩张（不一定 degree 1）。一般不存在环同构；
正确的 base change 应使用：
* place map `e : C3L.tensorIndex → Bad (...)` 满足 rational prime 兼容 `qVFamTensorP T (e i) = C3L.p`；
* 一个 **algebra map/embedding** `CommonPrimeCompletion(Fmod place) → rootNormedExtension`（或从 Fmod completion 到 F completion 的兼容映射），
  而不是 `rootBase ≃+* Fmod completion`；
* 用该 map 做 tensor base change（`rootExtension ⊗_{Fmod} ...` 或 fibers 替换 + transport），并证明 C3 region 在 base change 下的像；
* 因此 `BaseCompletionEquiv` 作为“new datum”不是合理的簿记；它把不同基域的 completion 直接等同，是**过强/可能 false 的前提**。

### 3.3 其他缺口

* `C3RootBlock := FinitePadicTensor (p := C3L.p) (fun i => RootFiber (e i))`：
  需要每个 `RootFiber` 是 `ℚ_[C3L.p]`-algebra；`rootNormedExtension` 的 scalar field 是 `ℚ_[qVFamTensorP]`；
  若 `qVFamTensorP ≠ C3L.p`，该定义类型不成立；文档没有给 p 兼容条件；
* 即使 p 相同，`C3RootBlock` 只是新块，没有从 `C3LogShellTensorBlockL` 到它的 base-change 映射；
  `rootThetaRegion` 如何从 C3 region 变换而来未定义；
* `u : C3RootBlock` 作为单位/乘法元素：`FinitePadicTensor` 有 CommRing（`FinitePadicTensorFieldDecomposition:25`），
  但 `QREGION-CONSTRUCT` 声称 C3 block “additive only, no ring/SMul”；这是另一个需核对的矛盾。
  若只有 additive 结构，`u • rootThetaRegion` 不能定义；若 `FinitePadicTensor` 的 CommRing 可用，则应明确使用哪个 instance，
  并证明它与 lana tensor 结构兼容；
* `haarLogVolume_mul_unit` 的一般 unit scaling law 未在 C3RootBlock 上专门化；文档列 batch L，尚未证；
* 没有构造/证明，所有体积/包含目标仍是后续；无循环，但**类型前提未闭合**。

### 3.4 Route B 判定

**PARTIAL / INVALID as written**：
* “type-correct in principle”**未成立**：`BaseCompletionEquiv` 把 F completion 与 Fmod completion 要求成环同构，一般不可能；
* p 兼容、region transport、ring/SMul instance、Haar scaling 均缺；
* 设计意图（base-change 而非 fake qroot action）正确，但必须改写为 algebra-map/base-change，不是 equiv；
* 无 CIRCULAR（未假设目标）；不存在把上界当下界的方向问题（文档未证不等式）。

## 4. 判定汇总

| 对象 | 判定 | 理由 |
|---|---|---|
| `ROOT-COMPLETION-MAP` | **PASS（分析级）** | 域不匹配结论成立；补强 F vs Fmod 不同 completion |
| `ROUTE-A-SCALAR` | **PARTIAL（含 INVALID 定理）** | badQ/target 正确；`S3050Unit_eq_log_norm_div` 符号错；GAPs 诚实；无循环 |
| `ROUTE-B-BASECHANGE` | **PARTIAL/INVALID as written** | `BaseCompletionEquiv` 过强/可能 false；p 兼容/transport/scaling 缺；设计意图可保留 |

**总判定：无 CIRCULAR；Route A 需修符号并把 GAP 降级；Route B 需把 equiv 改为 base-change algebra map 并补 p/transport。**

## 5. 修正建议

1. Route A：把 `S3050Unit_eq_log_norm_div` 改为 `= -Real.log ‖x‖/(2l)`；重新核对 `field_simp` 证明；
   未编译前不能称真证；GAP-SOURCE-ROOT/GAP-S2691/GAP-S3016 保留。
2. Route B：删除 `rootBase ≃+* CommonPrimeCompletion` 的 equiv 要求；改为：
   * `e` 的 p 兼容 `qVFamTensorP T (e i) = C3L.p`；
   * `CommonPrimeCompletion(Fmod place) → rootNormedExtension` 的 algebra map（经 F completion）；
   * tensor base change/region transport `C3 region → C3RootBlock region`；
   * `u` 的 ring/SMul 结构引用具体 instance；
   * Haar scaling law 先证 scalar/unit 情形，再推广。
3. 所有 Lean/gate 状态引用 watchdog/mainline；本审计不编译，相关文件 PENDING-WATCHDOG。