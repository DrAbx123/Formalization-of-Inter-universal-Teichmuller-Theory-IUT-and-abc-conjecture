# S1908：S1894 basis-independence 应用于 S1280 Gaussian 实际曲线；S1880 D5 clause / exact residual

日期：2026-11-01。任务：把 S1894 的 `S1894LargeImageInput` / `S1894SourceTorsionClause`
应用到 S1280 的实际 Gaussian 曲线（S1880 路线），给出 S1880 的 D5 clause 或 exact residual；
不得 fake。

## 结论（先给结果）

**S1894 的 basis-independence 完全适用于 S1280 Gaussian 曲线，但它只消去像域的
basis 依赖；S1880 的忠实 D5 clause 仍不能无条件构造。** 本包给出：

1. [已证] Gaussian 曲线的实际矩阵表示在不同 rank-two 基下只差一个实际
   `GL_2(F_l)` 共轭：`S1908MatrixRep_conj`、`S1908MatrixRep_range_conj`；
   因而 SL_2 包含条件与基无关：`S1908ImageTail_congr`。
2. [已证] 纸面存在性大像域
   `S1298LargeImageField l = SerreStyleLargeImageStatement E_G l`
   精确等于「rank-two 基 + S1894 basis-free 大像输入」：
   `S1908ExactMissing l ↔ S1298LargeImageField l`
   （`S1908ExactMissing_iff_serre`）。这里
   `S1908ExactMissing l = Nonempty (S1908TorsionBasis l) ∧ S1908LargeImageInput l`，
   `S1908LargeImageInput l = ∀ b, S1908ImageTail l b`。
3. [条件构造] 在 exact residual 下给出 S1880 D5 clause
   `S1908SourceTorsionClause`：
   - torsion carrier 是实际 Gaussian `mu_6` `S1298SixTorsionCarrier l`，
     带实际 primitive-root `Fin 6` label；
   - representation 是 `Q(i)` 的实际绝对 Galois 群与 `E_G[l]` 的实际
     mod-l 表示（range-restricted，故满射）；
   - image 域是 basis-free S1894 输入；给定 rank-two 基后等价于纸面
     `S1298LargeImageField`（`S1908SourceTorsionClause_image_iff`）；
   - six-torsion 域是字面纸面条件 (b) `Torsion23Rational E_G`
     （`S1637SixTorsionIndependent`）；
   - l-compatibility 域是字面条件 (c) `S1637LTorsionCompatible`。
   该 clause 供 `Nonempty (SourceTorsionClause l)`、S1880 first missing
   （`S1908S1880FirstMissing_nonempty`）以及 `S1280RemainingClauses` 的 D5 slot
   （`S1908RemainingClausesWithTorsion`）使用。
4. [已证] exact residual
   `S1908D5Residual l = S1908ExactMissing l ∧ S1637SixTorsionIndependent l ∧ S1637LTorsionCompatible l`
   精确等价于 S1637 忠实 gap 的非空性：
   `S1908D5Residual_iff_gap : S1908D5Residual l ↔ Nonempty (S1637D5Gap l)`；
   也等价于纸面大像域 + (b) + (c)（`S1908D5Residual_iff_serre`）。
   在 `l = 5` 该 residual 被形式化反驳
   （`S1908D5Residual_impossible_at_five`，来自 S1637 的实际 5-adic bad place）。

## 精确第一 missing

按 S1880 的 D5 分解，S1894 之后剩下的精确内容是：

1. `S1908ExactMissing l`：rank-two 基存在性 + basis-free 大像输入（Serre 型算术输入，
   树中无证明，本包只暴露不假设）；
2. `S1637SixTorsionIndependent l`：纸面条件 (b) `Torsion23Rational E_G`；
3. `S1637LTorsionCompatible l`：纸面条件 (c)，等价于 `l ≠ 5`（S1637 已证）。

其中 (3) 是纯算术可判定的；在 `l ≠ 5` 时自动成立。**(2) 是 S1894 完全无法消除的
curve-intrinsic 障碍**：S1637 §6 的 audit 已用 2-torsion 计算说明该条件对 Gaussian 曲线
实际上是**假的**——2-torsion 点为 `(x, -x/2)`，`4x^3 + x^2 + 20 = 0` 在 `Q(i)` 中无根
（该三次在 `Q` 上不可约；若一根在 `Q(i)\Q`，其共轭也是根，第三根
`-1/4 - z - \bar z` 落在 `Q`，矛盾）。该反驳**没有形式化**（树中也没有），所以本包
不声称 Gaussian D5 clause 无条件存在，也不把 six-torsion 域换成 True/PUnit/任意居民。
本包的 exact residual 就是上述三项；**S1880 的 D5 clause 在忠实语义下对这条 Gaussian
曲线为空**，S1894 只解决了像域的 basis 依赖，不能解决 (b)。

## 证据

- Lean：`tmp/sheaf/xif/paper/S1908S1280D5ImageActual.lean`
  - 451 行，20512 字节
  - SHA256 `C8466AA2EBEAC39F462D313D8C04C9962754B0716DBC8FDE4CB4A39681E225E4`
  - 编译：`EXIT=0`（第二次尝试；首次因并发构建的 Windows `.olean` 瞬时读取失败而退出 1，
    见下「并发说明」）
  - 成功编译日志无 error/warning；`#print axioms` 全部主定理仅
    `[propext, Classical.choice, Quot.sound]`（`S1908S1880FirstMissing_eq` 仅 `[propext]`），
    无 `sorryAx`、无自定义 axiom
- olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/S1908S1280D5ImageActual.olean`
  - 137272 字节，SHA256
    `DC4DCE34D1EACABA231E100BF103DBA47CA361755F09683BC24D8E815DCDCB3F`
  - import check：`tmp/sheaf/xif/paper/_S1908OleanCheck.lean` 直接 import 该 olean，
    `EXIT=0`，`#print axioms S1908D5Residual_iff_serre` 仅
    `[propext, Classical.choice, Quot.sound]`
- 本包未修改 `S1280SourceDefinition31Actual.lean`、`S1637D5TorsionClauseActual.lean`、
  `S1894D5LargeImageActual.lean`、`S1880OriginalXiFActual.lean`。
- 为避免重型 S1880 import，本文件把 S1880 的 D5 槽别名
  `S1880FirstMissing l`（definitionally `SourceTorsionClause l`）写成
  `S1908S1880FirstMissing l`；`S1880PaperClauseSupply l`（definitionally
  `S1280RemainingClauses l`）由 `S1908RemainingClausesWithTorsion` 直接填充。
  两处都是 definitional alias，不是新假设。

## 并发说明

共享工作区当时有 10+ 个 agent 同时编译重型文件；`lake env lean` 会阻塞在 Lake 锁上，
直接 `lean` 也偶发 `failed to read file ... .olean.private` 的瞬时 Windows IO 失败。
最终编译使用：

    $env:LEAN_PATH = '<mathlib build>;<project build>;<packages...>'
    & '<toolchain>\bin\lean.exe' -j1 -o <olean> <source>

第二次尝试成功；失败模式与文件内容/类型无关。

## 边界

- 未证明 `S1908LargeImageInput`（Serre 大像输入）；
- 未证明 `S1637SixTorsionIndependent`（纸面条件 (b)；S1637 audit 记为假，未形式化）；
- 未构造 D6/D7/D8 clause；未运行全 Project 构建、comparator 验收、独立人工审查；
- `target_accepted` 仍为 false；本包不改 `coord/STATE.md`、`coord/queue.md`、
  `AUDIT_LEDGER.md`（由协调层整合）。
